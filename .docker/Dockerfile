# This Dockerfile should be run from the root directory of this repo
# e.g. `docker build -f .docker/Dockerfile .` from the parent directory

FROM nixpkgs/nix-flakes

# See issue #71
RUN if [ "$(uname)" = Darwin ]; then \
    echo "filter-syscalls = false" >> /etc/nix/nix.conf; \
    fi

# Prepare the sources
COPY . /hax-sources
RUN cd /hax-sources && git init && git add .

# Use cache to speed up install
ENV PATH="$PATH:/root/.nix-profile/bin"
RUN nix-env -iA cachix -f https://cachix.org/api/v1/install
RUN cachix use hacspec

# Install
RUN nix profile install /hax-sources
