FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY ./polyreg.nix /tmp/polyreg.nix
COPY ./mona.nix    /tmp/mona.nix

RUN nix-env -i -f /tmp/polyreg.nix -A polyreg-devenv
RUN nix-collect-garbage -d
RUN rm -rf /tmp/polyreg-src/

WORKDIR /

ENTRYPOINT ["fish"]
