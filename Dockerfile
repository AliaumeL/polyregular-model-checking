FROM nixos/nix:latest AS builder

RUN nix-channel --update

COPY . /tmp/poly

WORKDIR /tmp/poly

RUN nix-build polyregular.nix -A polyreg-env -o result 

RUN mkdir -p /tmp/nix-polyreg-env/

RUN cp -R $(nix-store -qR result/) /tmp/nix-polyreg-env/

FROM scratch 

WORKDIR /app

COPY --from=builder /tmp/nix-polyreg-env/ /nix/store
COPY --from=builder /tmp/poly/result /app

ENTRYPOINT ["/app/bin/fish"]
