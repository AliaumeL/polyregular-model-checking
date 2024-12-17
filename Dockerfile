FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY . /tmp/polyreg-src/

WORKDIR /tmp/polyreg-src/

RUN nix-build polyreg.nix -A polyreg-devenv -o result 

RUN mkdir -p /tmp/nix-polyreg-env/

RUN cp -R $(nix-store -qR result/) /tmp/nix-polyreg-env/

FROM scratch 

WORKDIR /app

COPY --from=builder /tmp/nix-polyreg-env/ /nix/store
COPY --from=builder /tmp/polyreg-src/result /

ENTRYPOINT ["/bin/fish"]
