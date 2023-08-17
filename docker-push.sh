docker tag arkhive:$1 ghcr.io/meticulousmethods/arkhive:$1
docker push ghcr.io/meticulousmethods/arkhive:$1
docker tag arkhive:$1 ghcr.io/meticulousmethods/arkhive:latest
docker push ghcr.io/meticulousmethods/arkhive:latest