
docker run \
    -it \
    --rm \
    -v "${HOME}/Documents/ITMO:/publish/input" \
    -v "${PWD}/output:/publish/output" \
    -v "${PWD}/cache:/root/.org-timestamps" \
    -v "${PWD}/config:/publish/config" \
    org-publish
