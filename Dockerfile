FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY . /tmp/polyreg-src/

WORKDIR /tmp/polyreg-src/

RUN nix-env -i -f polyreg.nix -A polyreg-devenv
RUN nix-collect-garbage -d


ENTRYPOINT ["fish"]
