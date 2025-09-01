FROM icp-base:oopsla25 
COPY --chown=opam:opam . /home/build/icp-compcert
WORKDIR /home/build/icp-compcert
# Build CompCert
## Optional build argument to override architecture (full list in https://compcert.org/man/manual002.html)
ARG COMPCERT_TARGET
ENV COMPCERT_TARGET=${COMPCERT_TARGET:-auto}

## (auto-detect or override target)
RUN eval "$(opam env)" && \
  if [ "$COMPCERT_TARGET" = "auto" ]; then \
  TARGET=$(uname -m | sed -e 's/x86_64/x86_64-linux/' -e 's/aarch64/aarch64-linux/'); \
  else \
  TARGET=$COMPCERT_TARGET; \
  fi && \
  echo "Building CompCert for target: $TARGET" && \
  ./configure --ignore-coq-version $TARGET && \
  make -j"$(nproc --ignore=2)"

CMD ["bash"]
