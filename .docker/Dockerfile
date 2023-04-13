# This Dockerfile should be run from the root directory of this repo
# e.g. `docker build -f .docker/Dockerfile .` from the parent directory

FROM nixpkgs/nix-flakes

# Prepare the sources
COPY . /circus-sources
RUN cd /circus-sources && git init && git add .

# Install
RUN nix profile install /circus-sources
ENV PATH="$PATH:/root/.nix-profile/bin"
