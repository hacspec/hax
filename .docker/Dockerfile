# This Dockerfile should be run from the root directory of this repo
# e.g. `docker build -f .docker/Dockerfile .` from the parent directory

FROM ubuntu:24.04
# FROM nixpkgs/nix-flakes
LABEL maintainer="Franziskus Kiefer <franziskuskiefer@gmail.com>"

RUN apt-get update \
    && apt-get install -y \
    build-essential \
    opam \
    curl

ENV SHELL /bin/bash
ENV USER hax-user
ENV LOGNAME $USER
ENV HOME /home/$USER
ENV LANG en_US.UTF-8
ENV LC_ALL $LANG

RUN useradd -d $HOME -s $SHELL -m $USER
WORKDIR $HOME
USER $USER

# Install Rust
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
ENV PATH="$HOME/.cargo/bin:${PATH}"

# Prepare the sources
COPY . $HOME/hax
RUN cd $HOME/hax
RUN opam init --bare \
    && opam switch create 4.14.1 \
    && eval $(opam env)

# # Use cache to speed up install
# ENV PATH="$PATH:/root/.nix-profile/bin"
# RUN nix-env -iA cachix -f https://cachix.org/api/v1/install
# RUN cachix use hacspec

# Install
# RUN nix profile install /hax-sources
# RUN echo $PWD && ls -l
# RUN ./setup -j 10
