FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY ./polyreg.nix /tmp/polyreg.nix
COPY ./mona.nix    /tmp/mona.nix

RUN nix-env -i -f /tmp/polyreg.nix -A polyreg-devenv
RUN nix-collect-garbage -d

COPY . /tmp/polyreg-src/

WORKDIR /tmp/polyreg-src/polyreg
RUN stack build --only-dependencies --nix

RUN rm -rf /tmp/polyreg-src/

WORKDIR /

ENTRYPOINT ["fish"]
