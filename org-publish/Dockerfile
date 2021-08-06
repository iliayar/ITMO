FROM texlive/texlive:latest

RUN apt-get update && \
    apt-get install -y emacs

WORKDIR /publish

COPY packages.el packages.el
RUN emacs --batch -l /publish/packages.el

COPY entrypoint.sh entrypoint.sh
RUN chmod +x entrypoint.sh

ENTRYPOINT /publish/entrypoint.sh
