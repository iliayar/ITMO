docker run \
    -it \
    --rm \
    -v "${WORKSPACE}:/publish/input" \
    -v "/var/www/mainsite/public/public-notes/conspects:/publish/output" \
    -v "${WORKSPACE}/org-publish/cache:/root/.org-timestamps" \
    -v "${WORKSPACE}/org-publish/config:/publish/config" \
    org-publish
