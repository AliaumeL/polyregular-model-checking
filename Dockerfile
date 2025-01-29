FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY ./polycheck.nix /tmp/polycheck.nix
COPY ./mona.nix    /tmp/mona.nix

RUN nix-env -i -f /tmp/polycheck.nix -A polycheck-devenv
RUN nix-collect-garbage -d

WORKDIR /

ENTRYPOINT ["fish"]
