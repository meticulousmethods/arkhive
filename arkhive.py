#!/usr/bin/env python3

import argon2
from argon2.profiles import RFC_9106_LOW_MEMORY
import argparse
from bisect import bisect_left
from botocore.client import Config
from botocore.exceptions import ClientError
import boto3
import calendar
from collections import namedtuple
from Crypto.Cipher import ChaCha20_Poly1305
from Crypto.Random import get_random_bytes
from datetime import datetime, timezone
from dateutil.parser import parse as parse_date
from dateutil.relativedelta import relativedelta
from functools import reduce
import gzip
import hashlib
from io import BytesIO, SEEK_CUR, SEEK_END
import json
import msgpack
from multiprocessing import Lock, Pool
import operator
import os
from pathlib import Path, PurePath
from pid.decorator import pidfile
import re
import shutil
import subprocess
import sys
from tempfile import gettempdir, NamedTemporaryFile, _TemporaryFileWrapper
from urllib.request import urlopen


#
# Constants
#
CHUNK_SIZE = 10 * 1024 * 1024 # 10MB chunks
IN_MEMORY_MAX_SIZE = 100 * 1024 * 1024 # process files <= 100MB entirely in memory

STORAGES = [] # NOTE: populated below
CONFIG_ALL = [
    'encryption_password',
    'backup_processes',
    'restore_processes',
    'prune_days',
    'ignore_regex',
    'gzip_level',
    'compress',
    'encrypt',
    'pre_command',
    'success_url',
    ] # NOTE: extended by storages below


#
# Exceptions
#
class Error(Exception):
    pass


#
# Tuples
#
Dir = namedtuple('Dir', ['path', 'uid', 'gid', 'mode'])
File = namedtuple('File', ['path', 'size', 'modified', 'uid', 'gid', 'mode', 'hash'])
Symlink = namedtuple('Symlink', ['path', 'symlink', 'modified', 'uid', 'gid', 'mode'])


#
# Storages
#
class FilesystemStorage(object):
    """
    Storage for the local file system. 
    """
    ARGS = ['local_path']
    
    def __init__(self, local_path):
        self.path = Path(local_path)
    
    def init(self):
        """
        Initialise the storage. Only called once per run.
        """
        self.path.mkdir(parents=True, exist_ok=True)
    
    def list(self, rel_path=None, extension=None):
        """
        Iterates and yields StoragePath's for all files (optionally under the rel_path) 
        relative to the storage root.
        """
        path = (self.path / rel_path) if rel_path is not None else self.path
        
        for p in path.rglob('*%s' % extension if extension else '*'):
            stat = p.lstat()
            path = p.relative_to(self.path)

            if p.is_dir():
                yield Dir(path=str(path), uid=stat.st_uid, gid=stat.st_gid, mode=stat.st_mode)
                
            elif p.is_symlink():
                symlink = p.readlink()
                if symlink.is_relative_to(self.path):
                    symlink = symlink.relative_to(self.path)

                yield Symlink(path=str(path), symlink=str(symlink), modified=int(stat.st_mtime),
                    uid=stat.st_uid, gid=stat.st_gid, mode=stat.st_mode)
            
            else:
                yield File(path=str(path), size=stat.st_size, modified=int(stat.st_mtime), 
                    uid=stat.st_uid, gid=stat.st_gid, mode=stat.st_mode, hash=None)
    
    def read(self, path, size_hint):
        """
        Returns the data of the storage file as a file-like object.
        The file-like object must be compatible with close_io.
        """
        f = (self.path / path).open('rb')
        f.seek(0) # perform a seek so that we except here on unseekable files
        return f
    
    def write(self, path, f, metadata=None):
        """
        Atomically write a file object to the storage.
        """
        # ensure the parent folder(s) exit
        p = self.path / path
        p.parent.mkdir(parents=True, exist_ok=True)
        
        if isinstance(f, _TemporaryFileWrapper):
            pass # already a temporary file, so just rename it
        else:
            # store the data in a temporary file
            f.seek(0)
            f2 = NamedTemporaryFile(delete=False)
            for chunk in read_chunks(f):
                f2.write(chunk)
            f = f2
        
        # ensure the data is flushed to disk before we rename
        f.flush()
        os.fsync(f.fileno()) 
        f.close()
        
        # if we have a metadata, set the attributes before we move the file (for security)
        self._apply_metadata(f.name, metadata)
        
        # atomically rename the temporary file to our destination file
        os.rename(f.name, str(p))
    
    def mkdir(self, path, metadata=None):
        """
        Creates a directory if the storage supports it and sets optional metadata.
        """  
        p = self.path / path
        p.mkdir(parents=True, exist_ok=True)        
        self._apply_metadata(str(p), metadata)

    def symlink(self, path, symlink, metadata=None):
        """
        Creates a symlink at path pointing to symlink and sets optional metadata.
        """
        p = self.path / path
        p.parent.mkdir(parents=True, exist_ok=True)

        # symlinks can be absolute or relative to the storage root, so make absolute if relative
        symlink = Path(symlink)
        if not symlink.is_absolute():
            symlink = self.path / symlink
        
        p.unlink(missing_ok=True)
        p.symlink_to(symlink)
        self._apply_metadata(str(p), metadata, is_symlink=True)

    def copy(self, from_path, to_path, metadata=None):
        """
        Copies a path to a path and sets optional metadata.
        """
        from_p = self.path / from_path
        to_p = self.path / to_path
        to_p.parent.mkdir(parents=True, exist_ok=True)

        shutil.copy(str(from_p), str(to_p))
        self._apply_metadata(str(to_p), metadata)

    def exists(self, path):
        """
        Returns whether the path exists on the storage.
        """
        return (self.path / path).exists()

    def remove(self, *paths):
        """
        Removes one or more files from the storage.
        """
        for p in paths:
            (self.path / p).unlink()
    
    def _apply_metadata(self, file_name, metadata, is_symlink=False):
        """
        Private function that applies metadata to a file, directory or symlink.
        """
        # if we have a metadata, set the attributes before we move the file (for security)
        if metadata is not None:
            if getattr(metadata, 'modified', None) is not None:
                os.utime(file_name, (metadata.modified, metadata.modified), follow_symlinks=False)
            if (getattr(metadata, 'uid', None) is not None or 
                    getattr(metadata, 'gid', None) is not None):
                os.lchown(file_name, 
                    metadata.uid if getattr(metadata, 'uid', None) is not None else -1, 
                    metadata.gid if getattr(metadata, 'gid', None) is not None else -1)
            if getattr(metadata, 'mode', None) is not None:
                if is_symlink:
                    # linux doesn't support lchmod, but it doesn't use symlink permissions anyway
                    if hasattr(os, 'lchmod'):
                        os.lchmod(file_name, metadata.mode)
                else:
                    os.chmod(file_name, metadata.mode)

STORAGES.append(FilesystemStorage)


class S3Storage(object):
    """
    Storage for an s3 bucket. 
    """
    ARGS = ['aws_access_key_id', 'aws_secret_access_key', 's3_bucket', 'base_path', 'endpoint_url',
        'signature_version', 'region_name', 'storage_class']
    
    def __init__(self, aws_access_key_id, aws_secret_access_key, s3_bucket, base_path=None,
            endpoint_url=None, signature_version=None, region_name=None,
            storage_class=None):
        self.s3_args = {
            'aws_access_key_id': aws_access_key_id, 
            'aws_secret_access_key': aws_secret_access_key,
            'signature_version': signature_version,
            'endpoint_url': endpoint_url,
            'region_name': region_name,
            }
        self.s3_bucket = s3_bucket
        self.base_path = PurePath((base_path or '').lstrip('/'))
        self.storage_class = storage_class
    
    def init(self):
        """
        Initialise the storage. Only called once per run.
        """
        # create the bucket if it doesn't exist
        bucket = self._bucket()
        args = {'Bucket': bucket.name}
        try:
            bucket.meta.client.head_bucket(**args)
        except ClientError as e:
            if e.response['Error']['Code'] == "404":
                log('Bucket "%s" does not exist. Creating...' % bucket.name)
                if self.s3_args['region_name']:
                    args.update({
                        'CreateBucketConfiguration': {
                            'LocationConstraint': self.s3_args['region_name'],
                            },
                        })
                bucket.meta.client.create_bucket(**args)
            else:
                raise
    
    def list(self, rel_path=None, extension=None):
        """
        Iterates and yields StoragePath's for all files (optionally under the rel_path) 
        relative to the storage root.
        """
        path = (self.base_path / rel_path) if rel_path is not None else self.base_path
        
        if str(path) != '.':
            it = self._bucket().objects.filter(**{
                'Prefix': str(path) + '/',
                })
        else:
            it = self._bucket().objects.all()
        
        for count, obj in enumerate(it, start=1):
            if count % 10000 == 0:
                log('Listed %s files...' % count)
            if obj.key.endswith('/'):
                continue # ignore folders
            p = PurePath(obj.key).relative_to(self.base_path)
            if extension is None or p.suffix == extension:
                yield File(path=str(p), size=obj.size, 
                    modified=datetime_to_int(obj.last_modified), 
                    uid=None, gid=None, mode=None, hash=None)
        
    def read(self, path, size_hint):
        """
        Returns the data of the storage file as a file-like object.
        The file-like object must be compatible with close_io.
        """
        f = open_temp_io(size_hint)
        self._bucket().download_fileobj(str(self.base_path / path), f)
        return f

    def write(self, path, f, metadata=None):
        """
        Atomically write the data to the storage.
        """
        f.seek(0)
        args = {'ExtraArgs': {'StorageClass': self.storage_class}} if self.storage_class else {}
        self._bucket().upload_fileobj(f, str(self.base_path / path), **args)
    
    def mkdir(self, path, metadata=None):
        """
        Creates a directory if the storage supports it and sets optional metadata.
        """  
        pass
    
    def symlink(self, path, symlink, metadata=None):
        """
        Creates a symlink at path pointing to symlink and sets optional metadata.
        """
        pass
    
    def copy(self, from_path, to_path, metadata=None):
        """
        Copies a path to a path and sets optional metadata.
        """
        self._bucket().copy({
            'Bucket': self.s3_bucket,
            'Key': str(self.base_path / from_path),
            }, str(self.base_path / to_path))

    def exists(self, path):
        """
        Returns whether the path exists on the storage.
        """
        client = self._bucket().meta.client
        try:
            client.head_object(**{
                'Bucket': self.s3_bucket,
                'Key': str(self.base_path / path),
                })
        except ClientError as e:
            if e.response['Error']['Code'] == "404":
                return False
            raise
        else:
            return True
    
    def remove(self, *paths):
        """
        Removes one or more files from the storage.
        """
        self._bucket().delete_objects(**{
            'Delete': {'Objects': [{'Key': str(self.base_path / p) for p in paths}]}})
    
    def _bucket(self):
        """
        Internally used to return the boto3 bucket.
        """
        args = dict(self.s3_args)
        config = Config(
            retries={
                'total_max_attempts': 10,
                'mode': 'adaptive',
                },
            signature_version=args.pop('signature_version'))
        s3 = boto3.resource('s3', **dict(args, config=config))
        return s3.Bucket(self.s3_bucket)


STORAGES.append(S3Storage)

CONFIG_ALL.extend(
    reduce(operator.add, [['src.%s' % a for a in s.ARGS] for s in STORAGES]) +
    reduce(operator.add, [['dest.%s' % a for a in s.ARGS] for s in STORAGES]) +
    reduce(operator.add, [['restore.%s' % a for a in s.ARGS] for s in STORAGES])
    )


#
# Files
#
class BaseFile(object):
    """
    Represents a compressed and encrypted file.
    """
    BASE_MAGIC_BYTES = hashlib.sha256(b'arkhive').digest()[::4]
    GZIP_MAGIC_BYTES = BASE_MAGIC_BYTES + b'GZIP'
    XCHA_MAGIC_BYTES = BASE_MAGIC_BYTES + b'XCHA'

    @classmethod
    def compress_encrypt(cls, config, original_io):
        """
        Compresses and encrypts an IO and returns the result as a temporary IO.
        """
        original_size = io_size(original_io)

        if as_bool(config.get('compress', True)):
            # compress the data using gzip
            original_io.seek(0)
            compressed_io = open_temp_io(original_size)
            compressed_io.write(cls.GZIP_MAGIC_BYTES)

            with gzip.GzipFile(fileobj=compressed_io, mode='wb', 
                    compresslevel=int(config.get('gzip_level') or 6)) as f:
                for chunk in read_chunks(original_io):
                    f.write(chunk)
            
            close_io(original_io)
        else:
            compressed_io = original_io
        
        compressed_size = io_size(compressed_io)

        if as_bool(config.get('encrypt', True)):
            # encrypt the data using xchacha-poly
            key, salt = config_encryption_key(config)
            nonce = get_random_bytes(24) # XChaCha20-Poly1305 is 24
            cipher = ChaCha20_Poly1305.new(key=key, nonce=nonce)

            compressed_io.seek(0)
            encrypted_io = open_temp_io(compressed_size)
            encrypted_io.write(cls.XCHA_MAGIC_BYTES)
            encrypted_io.write(salt)
            encrypted_io.write(nonce)
            encrypted_io.seek(16, SEEK_CUR) # leave 16 bytes for the digest
            
            for chunk in read_chunks(compressed_io):
                encrypted_io.write(cipher.encrypt(chunk))
            
            encrypted_io.seek(len(cls.XCHA_MAGIC_BYTES) + len(salt) + len(nonce))
            encrypted_io.write(cipher.digest())

            close_io(compressed_io)
        else:
            encrypted_io = compressed_io
        
        return encrypted_io
    
    @classmethod
    def decrypt_decompress(cls, config, encrypted_io):
        """
        Decrypts and decompresses an IO and returns the result as a temporary IO.
        """
        encrypted_size = io_size(encrypted_io)
        encrypted_io.seek(0)
        magic_bytes = encrypted_io.read(len(cls.XCHA_MAGIC_BYTES))

        if magic_bytes == cls.XCHA_MAGIC_BYTES:
            # decrypt the data using xchacha-poly
            key, salt = config_encryption_key(config, encrypted_io.read(16))
            cipher = ChaCha20_Poly1305.new(key=key, 
                nonce=encrypted_io.read(24)) # XChaCha20-Poly130 is 24  
            digest = encrypted_io.read(16)
            
            compressed_io = open_temp_io(encrypted_size)

            for chunk in read_chunks(encrypted_io):
                compressed_io.write(cipher.decrypt(chunk))
            
            cipher.verify(digest)            

            close_io(encrypted_io)
        else:
            compressed_io = encrypted_io
        
        compressed_size = io_size(compressed_io)
        compressed_io.seek(0)
        magic_bytes = compressed_io.read(len(cls.GZIP_MAGIC_BYTES))

        if magic_bytes == cls.GZIP_MAGIC_BYTES:
            # decompress the data using gzip
            original_io = open_temp_io(compressed_size)
            
            with gzip.GzipFile(fileobj=compressed_io, mode='rb') as f:
                for chunk in read_chunks(f):
                    original_io.write(chunk)            

            close_io(compressed_io)
        else:
            original_io = compressed_io
        
        return original_io


class BackupFile(BaseFile):
    """
    Represents the state of a backup including all files, folders, symlinks and their metadata.
    """
    BASE_PATH = 'backups/'
    EXTENSION = '.bf'
    VERSION = 1
    DATE_FORMAT = '%Y%m%d-%H%M%S'
    
    def __init__(self, version=None, dirs=None, files=None, symlinks=None):
        self.version = version or self.VERSION
        self.dirs = [Dir(*s) for s in dirs or []]
        self.files = [File(*s) for s in files or []]
        self.symlinks = [Symlink(*s) for s in symlinks or []]
    
    #
    # Backup creation
    #
    def make_path(self):
        """
        Returns the relative path on the storage where the backup should be stored.
        """
        return str(PurePath(self.BASE_PATH) / 
            (datetime.now(timezone.utc).strftime(self.DATE_FORMAT) + self.EXTENSION))
    
    def dump(self, config):
        """
        Writes the state to a temporary file object and returns it.
        """
        io = open_temp_io(0) # always make in-memory
        msgpack.dump((self.version, self.dirs, self.files, self.symlinks), io)
        return self.compress_encrypt(config, io)
    
    def add_dir(self, dir):
        """
        Adds a Dir to the backup state.
        """
        self.dirs.append(dir)
    
    def add_file(self, file):
        """
        Adds a File to the backup state.
        """
        self.files.append(file)
    
    def add_symlink(self, symlink):
        """
        Adds a Symlink to the backup state.
        """
        self.symlinks.append(symlink)

    #
    # Backup processing
    #
    @classmethod
    def parse_date_from_path(cls, path):
        """
        Returns the date for a given backup from it's path.
        """
        return datetime.strptime(PurePath(path).stem, cls.DATE_FORMAT).replace(tzinfo=timezone.utc)

    @classmethod
    def load(cls, config, io):
        """
        Load the state from a file object.
        """
        io = cls.decrypt_decompress(config, io)
        io.seek(0)
        res = cls(*msgpack.load(io))
        close_io(io)
        return res    

    @property
    def psm_to_file(self):
        """
        Lazy property that returns a dictionary of (path, size, modified) to File.
        """
        # lazily build the lookup
        if not hasattr(self, '_psm_to_file'):
            self._psm_to_file = {(f.path, f.size, f.modified): f for f in self.files}
        return self._psm_to_file

    @property
    def hashes(self):
        """
        Property that returns all hashes of the backup as a set.
        """
        if not hasattr(self, '_hashes'):
            self._hashes = {f.hash for f in self.files}
        return self._hashes
        
    @property
    def hash_to_files(self):
        """
        Property that returns a dictionary of hash to each file that references that hash.
        """
        # lazily build the lookup
        if not hasattr(self, '_hash_to_files'):
            self._hash_to_files = reduce(dict_values_list, [(f.hash, f) for f in self.files], {})
        return self._hash_to_files


class HashFile(BaseFile):
    """
    Represents a file on the storage represented by the files original 
    base36 encoded hash as it's filename.
    """
    BASE_PATH = 'files/'
    EXTENSION = '.hf'

    @classmethod
    def make_path(cls, hash):
        """
        Returns the relative path to the HashFile on the storage for a given hash.
        """
        return str(PurePath(cls.BASE_PATH) / hash[0] / hash[1] / hash[2] / 
            (hash[3:] + cls.EXTENSION))

    @classmethod
    def from_original(cls, config, original_io):
        """
        Creates a new HashFile from an original file by compressing and encrypting it.
        """
        return cls.compress_encrypt(config, original_io)
    
    @classmethod
    def to_original(cls, config, encrypted_io):
        """
        Decrypts and decompressed the HashFile and returns a temporary IO 
        containing the original file.
        """
        return cls.decrypt_decompress(config, encrypted_io)


#
# Backup functions
#
_backup_state = None


def init_backup_state(config, src_storage, dest_storage, last_backup):
    """
    Initialises the state of the multiprocessing process for backup_file.
    """
    global _backup_state
    _backup_state = {'config': config, 'src_storage': src_storage, 'dest_storage': dest_storage,
        'last_backup': last_backup}


def backup_file(index, file):
    """
    Downloads the file from the source, calculates it's hash, and determines whether it needs
    to be uploaded to the destination storage. If it does, it uploads it.
    The path with the hash is then returned.
    """
    config = _backup_state['config']
    src_storage = _backup_state['src_storage']
    dest_storage = _backup_state['dest_storage']
    last_backup = _backup_state['last_backup']
    
    log('[%s] Hashing %s...' % (index, file.path))

    # read the file and determine it's hash
    try:
        original_io = src_storage.read(file.path, file.size)
    except Exception as e:
        raise Error('[%s] Failed to retrieve %s from source storage. %s %s' % (
            index, file.path, type(e), str(e)))
    
    with auto_close(original_io):
        # TODO: check modified date before and after and if it changed then
        # delete the hash file and reupload again until post-upload the modified date is the same
        # this ensures we haven't uploaded modified data
        # fail after X number of retries

        # TODO: output local time without timezone

        hash, size = base36_sha256_hash_and_size(original_io)
        if file.size != size:
            raise Error('[%s] Size mismatch for %s. Expected %s, got %s.' % (
                index, file.path, file.size, size))
        
        # if we don't have a last backup, or the hash wasn't in the previous backup
        if last_backup is None or hash not in last_backup.hashes: 
            # check whether the hash exists on the destination storage
            hash_path = HashFile.make_path(hash)
            
            if dest_storage.exists(hash_path):
                log('[%s] Hash %s already exists at destination. Skipping transfer.' % (
                    index, hash))
            else:
                log('[%s] Backing up %s...' % (index, file.path))
                # file doesn't exist on storage, so compress+encrypt it then upload
                encrypted_io = HashFile.from_original(config, original_io) # closes original_io
                with auto_close(encrypted_io):
                    try:
                        dest_storage.write(hash_path, encrypted_io, metadata=file)
                    except Exception as e:
                        raise Error('[%s] Failed to write %s to destination storage. %s %s' % (
                            index, hash_path, type(e), str(e)))
    
    return file._replace(hash=hash)


def do_backup(config, src_storage, dest_storage):
    """
    Performs a backup to the storage.
    """
    config_encryption_key(config) # generate a salt+key to be used by all processes
    
    # inner helper function that loads a backup from the destination storage
    def load_backup(path):
        try:
            backup_io = dest_storage.read(path.path, path.size)
        except Exception as e:
            fail('Failed to retrieve %s from destination storage. %s %s' % (
                path.path, type(e), str(e)))
        return BackupFile.load(config, backup_io) # closes backup_io

    # list all previous backups and load the latest backup
    log('Listing previous backups on destination storage...')

    backups = sorted([(BackupFile.parse_date_from_path(p.path), p) 
            for p in dest_storage.list(BackupFile.BASE_PATH, BackupFile.EXTENSION)])
    
    last_backup_path = None
    last_backup = None
    if backups:
        last_backup_date, last_backup_path = backups[-1]
        log('Using last backup %s as reference.' % last_backup_date.astimezone().isoformat())
        last_backup = load_backup(last_backup_path)
    
    errors = 0
    new_backup = BackupFile()

    with Pool(int(config.get('backup_processes') or 4), initializer=init_backup_state, 
            initargs=(config, src_storage, dest_storage, last_backup)) as pool:
        processes = []
        
        # list all source files
        log('Listing files on source storage...')

        ignore_regexes = [re.compile(r) for r in config.get('ignore_regex', [])]

        for index, path in enumerate(src_storage.list(), start=1):
            if any(r.match(path.path) for r in ignore_regexes):
                continue
            
            # if the path is a directory or symlink, simply store it in the new backup 
            # as we don't need to do any uploading for these
            if isinstance(path, Dir):
                new_backup.add_dir(path)
                continue
            elif isinstance(path, Symlink):
                new_backup.add_symlink(path)
                continue
            
            # if the file existed at the exact same path, size and modification date
            # last backup then we can simply store it in the new backup and continue
            if last_backup is not None:
                last_file = last_backup.psm_to_file.get((str(path.path), path.size, path.modified))
                if last_file is not None:
                    new_backup.add_file(last_file)
                    continue
            
            # file is new or has changed since last backup so perform the backup in another process
            processes.append(pool.apply_async(backup_file, [index, path]))
        
        log('Listing source complete!')

        # wait for all processes to finish and raise any exceptions they raise
        if processes:
            log('Waiting for backups to complete...')
            for process in processes:
                try:
                    new_backup.add_file(process.get()) # re-raises any exceptions
                except Error as e:
                    err(e)
                    errors += 1
        else:
            log('No modified files to backup.')

        # atomically write the backup state file which signals a successful backup
        dest_storage.write(new_backup.make_path(), new_backup.dump(config))
    
    # determine if we should prune by comparing backups against the prune date
    today = datetime.now(timezone.utc).astimezone().replace(
        hour=0, minute=0, second=0, microsecond=0)
    prune_date = (today - relativedelta(days=int(config.get(
        'prune_days', 7)))).astimezone(timezone.utc)
    
    prune_index = bisect_left(backups, prune_date, key=lambda b: b[0])
    prune_backups, keep_backups = backups[:prune_index], backups[prune_index:]
    
    if prune_backups:
        log('Starting prune.')

        # load all previous backups one by one and
        # build a set of all hashes from all backups to be kept
        log('Determining hashes to prune.. This can take a while.')

        keep_hash = set()
        keep_hash.update(new_backup.hashes)
        
        for unused, backup_path in keep_backups:
            backup = last_backup if backup_path == last_backup_path else load_backup(backup_path)
            keep_hash.update(backup.hashes)
        
        # for all hashes from all backups to be pruned, if they aren't in the keep hash set
        # then the hash can be deleted
        delete_hash = set()

        for unused, backup_path in prune_backups:
            backup = last_backup if backup_path == last_backup_path else load_backup(backup_path)
            delete_hash.update(backup.hashes - keep_hash)

        # delete the backups
        for backup_date, backup_path in prune_backups:
            log('Pruning backup %s...' % backup_date.astimezone().isoformat())
            dest_storage.remove(backup_path.path)

        # delete the hashes
        for hash in delete_hash:
            log('Pruning hash %s...' % hash)
            dest_storage.remove(HashFile.make_path(hash))

    # notify the success URL if there was no errors
    if not errors and config.get('success_url'):
        log('Notifying success URL...')
        urlopen(config['success_url'])

    log('Done!')
    if errors:
        fail('%s error(s) occurred during backup.' % errors)


#
# List backup functions
#
def do_list_backups(config, dest_storage):
    """
    List the dates of all backups in the users local time.
    """
    log('Listing previous backups on destination storage...')

    backups = sorted([(BackupFile.parse_date_from_path(p.path), p) 
        for p in dest_storage.list(BackupFile.BASE_PATH, BackupFile.EXTENSION)])    
    
    for backup_date, backup_path in backups:
        log('%s' % backup_date.astimezone().isoformat())
    
    log('Done!')


#
# Restore functions
#
_restore_state = None


def init_restore_state(config, dest_storage, restore_storage, verify):
    """
    Initialises the state of the multiprocessing process for restore_hash.
    """
    global _restore_state
    _restore_state = {'config': config, 'dest_storage': dest_storage, 
        'restore_storage': restore_storage, 'verify': verify}
    

def restore_hash(index, hash, files):
    """
    Downloads a hash from the destination and writes it to the files in the restore storage.
    Alternately if we are verifying no writing is performed.
    """
    config = _restore_state['config']
    dest_storage = _restore_state['dest_storage']
    restore_storage = _restore_state['restore_storage']
    verify = _restore_state['verify']

    log(('[%s] Verifying %s...' if verify else '[%s] Restoring %s...') % (
        index, ', '.join(f.path for f in files)))

    # download the hashed file from the destination storage and decrypt+decompress it
    hash_path = HashFile.make_path(hash)

    try:
        encrypted_io = dest_storage.read(hash_path, files[0].size)
    except Exception as e:
        raise Error('[%s] Failed to retrieve %s from destination storage. %s %s' % (
            index, hash_path, type(e), str(e)))
    
    original_io = HashFile.to_original(config, encrypted_io) # closes encrypted_io

    with auto_close(original_io):
        if verify:
            # verify the hash of the file against what is expected
            # kind of redundant with encryption, and even compression, but the user might have
            # disabled both, or want to be doubly sure their backup is integral
            hash_, size = base36_sha256_hash_and_size(original_io)
            if hash != hash_:
                raise Error('[%s] Hash mismatch. Expected %s found %s for %s' % (
                    index, hash, hash_, ', '.join(f.path for f in files)))
            
        else:
            # write the first file to the restore storage and then copy it to any other files
            # copying is faster than writing the file multiple times, especially for remote storages
            try:
                restore_storage.write(files[0].path, original_io, metadata=files[0])
            except Exception as e:
                raise Error('[%s] Failed to write %s to restore storage. %s %s' % (
                    index, files[0].path, type(e), str(e)))
            
            failed = []
            for file in files[1:]:
                try:
                    restore_storage.copy(files[0].path, file.path, metadata=file)
                except Exception as e:
                    failed.append(file.path)
            if failed:
                raise Error('[%s] Failed to write %s to restore storage. %s %s' % (
                    index, ', '.join(failed), type(e), str(e)))


def do_restore(config, dest_storage, restore_storage=None, restore_date=None, restore_regex=None, 
        verify=False):
    """
    Performs a restore from the destination storage to the restore storage.
    """
    if restore_date is not None:
        try:
            restore_date = parse_date(restore_date)
        except Exception:
            fail('The restore date is not a valid date!')

    # list all previous backups, find the corresponding backup to use and load it
    log('Listing previous backups on destination storage...')

    backups = sorted([(BackupFile.parse_date_from_path(p.path), p) 
            for p in dest_storage.list(BackupFile.BASE_PATH, BackupFile.EXTENSION)],
        reverse=True)
    if not backups:
        fail('No previous backups found!')

    backup_path = None
    for backup_date, backup_path in backups:
        if restore_date is None or restore_date >= backup_date:
            break
    if backup_path is None:
        fail('No backup found that satisfies the restore date! Try a different date.')
    
    log('Using backup %s.' % backup_date.astimezone().isoformat())

    try:
        backup_io = dest_storage.read(backup_path.path, backup_path.size)
    except Exception as e:
        fail('Failed to retrieve %s from destination storage. %s %s' % (
            backup_path.path, type(e), str(e)))
    backup = BackupFile.load(config, backup_io) # closes backup_io
    
    errors = 0

    if not verify:
        restore_regexes = [re.compile(r) for r in restore_regex or []]
        
        # restore directories and symlinks first
        # we restore directories first for security so that all folder permissions are correct
        # before restoring files into those folders
        log('Restoring directories and symlinks...')

        for dir in backup.dirs:
            if (restore_regexes and not any(
                    r.match(dir.path) or r.match(dir.path + PurePath(dir.path)._flavour.sep)
                    for r in restore_regexes)):
                continue

            try:
                restore_storage.mkdir(dir.path, metadata=dir)
            except Exception as e:
                err('Failed to make directory %s on restore storage. %s %s' % (
                    dir.path, type(e), str(e)))
                errors += 1
        
        for symlink in backup.symlinks:
            if restore_regexes and not any(r.match(symlink.path) for r in restore_regexes):
                continue

            try:
                restore_storage.symlink(symlink.path, symlink.symlink, metadata=symlink)
            except Exception as e:
                err('Failed to make symlink %s on restore storage. %s %s' % (
                    symlink.path, type(e), str(e)))
                errors += 1

    with Pool(int(config.get('restore_processes') or 4), initializer=init_restore_state, 
            initargs=(config, dest_storage, restore_storage, verify)) as pool:
        processes = []
        
        # group all files by hash and download each hash from the source once
        log(('Verifying %s files...' if verify else 'Restoring %s files...') % len(backup.files))
        
        for index, (hash, files) in enumerate(backup.hash_to_files.items(), start=1):
            if not verify and restore_regexes:
                files = [f for f in files if any(r.match(f.path) for r in restore_regexes)]
                if not files:
                    continue
            
            processes.append(pool.apply_async(restore_hash, [index, hash, files]))

        for process in processes:
            try:
                process.get() # re-raises any exceptions
            except Error as e:
                err(e)
                errors += 1
    
    log('Done!')
    if errors:
        fail('%s error(s) occurred during restore.' % errors)


#
# Common functions
#
def config_encryption_key(config, salt=None):
    """
    Returns the encryption key and salt used for the password defined in the config.
    If no salt is provided, then a salt is generated for this run. 
    Otherwise returns the key for that salt.
    """
    if salt is None:
        # only determine the salt used to encrypt objects once per run
        salt = config.get('_encryption_salt')
        if salt is None:
            salt = config['_encryption_salt'] = get_random_bytes(16)

    # only determine the key for a given salt once per run
    key = config.get('_encryption_key', {}).get(salt)
    if key is None:
        config.setdefault('_encryption_key', {})
        key = config['_encryption_key'][salt] = \
            argon2_key(config['encryption_password'], salt)
    
    return key, salt


#
# Utility functions
#
print_lock = Lock()


def log(msg, file=None):
    """
    Log's a message.
    """
    msg = '[%s] %s' % (datetime.now().isoformat(timespec='seconds'), msg)
    with print_lock:
        print(msg, flush=True)


def err(msg):
    """
    Logs an error and raises an exception.
    """
    log(msg, file=sys.stderr)


def fail(msg):
    """
    Displays an error and exits the program.
    """
    sys.exit(msg)


def as_bool(v):
    """
    Returns a value as a boolean value. Handles strings that represent boolean values.
    """
    if isinstance(v, str):
        return v.lower() not in ('no', 'false', 'n', 'f', '0', '')
    return bool(v)


def read_chunks(f):
    """
    Reads in chunks of a file and yields the chunk.
    """
    while True:
        data = f.read(CHUNK_SIZE)
        if not data:
            break
        yield data


def io_size(f):
    """
    Returns the file size for a given file-like object.
    """
    f.seek(0, SEEK_END)
    return f.tell()


def open_temp_io(size_hint):
    """
    Opens a temporary file-like object depending on the size of the data to be stored.
    """
    if size_hint <= IN_MEMORY_MAX_SIZE:
        return BytesIO()
    else:
        return NamedTemporaryFile(delete=False)


def close_io(f):
    """
    Closes a temporary file-like object opened using open_temp_io, or other file-like objects.
    """
    f.close()
    if isinstance(f, _TemporaryFileWrapper) and not f.delete and os.path.exists(f.name):
        os.remove(f.name)


class auto_close(object):
    """
    Calls close_io automatically when the with statement exits.
    """
    def __init__(self, io):
        self.io = io
    
    def __enter__(self):
        pass

    def __exit__(self, exc_type, exc_val, exc_tb):
        close_io(self.io)


def base36_sha256_hash_and_size(f):
    """
    Calculates the SHA256 hash of a file-like object (as an integer).
    """
    f.seek(0)
    
    h = hashlib.sha256()
    size = 0
    for chunk in read_chunks(f):
        h.update(chunk)
        size += len(chunk)
    
    return int_to_base36(int.from_bytes(h.digest(), 'big')), size


def argon2_key(encryption_password, salt):
    """
    Generates an encryption key from a password using the Argon2id KDF.
    """
    return argon2.low_level.hash_secret_raw(encryption_password.encode('utf-8'), salt, 
        time_cost=RFC_9106_LOW_MEMORY.time_cost, memory_cost=RFC_9106_LOW_MEMORY.memory_cost, 
        parallelism=RFC_9106_LOW_MEMORY.parallelism, hash_len=32, type=argon2.low_level.Type.ID)


def int_to_base36(i):
    """
    Convert an integer to a base36 string.
    """
    chars = "0123456789abcdefghijklmnopqrstuvwxyz"
    if i < 36:
        return chars[i]
    
    s = ""
    while i != 0:
        i, n = divmod(i, 36)
        s = chars[n] + s
    
    return s


def dict_values_list(d, x):
    """
    Function for reduce, that reduces a list of k,v tuples to a dictionary that contains a 
    list of the values for each given key.
    eg. reduce(dict_values_list, [('a', 1), ('a', 2)], {}) -> {'a': [1, 2]} 
    """
    k, v = x
    if k not in d:
        d[k] = [v]
    else:
        d[k].append(v)
    return d


def datetime_to_int(d):
    """
    Converts a date to a UTC epoch integer.
    """
    return calendar.timegm(d.astimezone(timezone.utc).timetuple())


#
# Main
#
@pidfile()
def main():
    """
    Runs the backup, verify or restore.
    """
    log('arkhive started.')
    
    # parse the command-line arguments
    parser = argparse.ArgumentParser()
    parser.add_argument('--config', default='config.json',
        help='Specify the path to the config file.')
    parser.add_argument('--list-backups', action='store_true',
        help='Lists all existing backups by date. These dates should be given to --restore-date.')
    parser.add_argument('--verify', action='store_true',
        help='Verifies the integrity of a backup by decrypting and verifying hashes.')
    parser.add_argument('--restore', action='store_true',
        help='Perform a restore instead of a backup.')
    parser.add_argument('--restore-date', action='store',
        help='Specifies a date to restore to. The closest backup to this date will be chosen. '
            'If not specified, the latest backup is used.')
    parser.add_argument('--restore-regex', action='append',
        help='Specifies file(s) to only restore via regular expression. Other files will be ignored.')
    args = parser.parse_args()
    
    # load the configuration via environment variables, if any are set
    config = {}
    env_used = False
    
    for arg in CONFIG_ALL:
        env_name = arg.upper().replace('.', '_')
        
        if os.environ.get(env_name):
            env_used = True
            
            if '.' in arg:
                parent, arg = arg.split('.', 1)
                obj = config.setdefault(parent, {})
            else:
                obj = config
            
            value = os.environ[env_name]
            if value.startswith('['):
                value = json.loads(value) # envarg arrays should be defined as json
            
            obj[arg] = value
    
    # if no environment variables were found, then load via the json config file
    if not env_used:  
        with open(args.config, 'rb') as f:
            config = json.load(f)
    
    # if defined, execute a command before running the backup
    if config.get('pre_command'):
        log('Running pre-command...')
        subprocess.run(config['pre_command'], shell=True)
        log('Pre-command done!')

    # load all storages
    if not config.get('restore'):
        config.setdefault('restore', {})['local_path'] = str(Path(gettempdir()) / 'arkhive_restore')
    
    for storage_class in STORAGES:
        if any(a in config['src'] for a in storage_class.ARGS):
            src_storage = storage_class(**config['src'])
        if any(a in config['dest'] for a in storage_class.ARGS):
            dest_storage = storage_class(**config['dest'])
        if any(a in config['restore'] for a in storage_class.ARGS):
            restore_storage = storage_class(**config['restore'])
    
    dest_storage.init()
    
    # perform the backup or restore
    if args.list_backups:
        do_list_backups(config, dest_storage)
    elif args.verify:
        do_restore(config, dest_storage, verify=True)
    elif args.restore:
        restore_storage.init()
        do_restore(config, dest_storage, restore_storage=restore_storage, 
            restore_date=args.restore_date, restore_regex=args.restore_regex)
    else:
        src_storage.init()
        do_backup(config, src_storage, dest_storage)


if __name__ == '__main__':
    sys.exit(main())