# This Dockerfile should be run from the root directory of this repo
# e.g. `docker build -f .docker/Dockerfile . -t hax` from the parent directory

FROM ubuntu:24.04
LABEL maintainer="Franziskus Kiefer <franziskuskiefer@gmail.com>"

RUN apt-get update
RUN apt-get install -y \
    nodejs \
    build-essential \
    opam \
    jq \
    libgmp-dev \
    locales \
    curl
RUN curl -fsSL https://deb.nodesource.com/setup_21.x | bash -
RUN apt-get update && apt-get install -y nodejs

ENV SHELL /bin/bash
ENV USER hax-user
ENV LOGNAME $USER
ENV HOME /home/$USER
ENV LANG en_US.UTF-8
ENV LC_ALL $LANG

RUN locale-gen $LANG && DEBIAN_FRONTEND=noninteractive dpkg-reconfigure locales

RUN useradd -d $HOME -s $SHELL -m $USER
RUN echo "$USER:$USER" | chpasswd && adduser $USER sudo
WORKDIR $HOME
USER $USER

# Install Rust
RUN curl https://sh.rustup.rs -sSf | bash -s -- -y
ENV PATH="$HOME/.cargo/bin:${PATH}"

# Prepare the sources
COPY --chown=hax-user:hax-user . $HOME/hax
RUN opam init --bare --disable-sandboxing && \
    opam switch create 4.14.1 && \
    eval $(opam env)
RUN cd $HOME/hax && ./setup.sh -j 2
RUN echo "eval $(opam env)" >> $HOME/.bashrc

# Get F* and HACL* for running proofs
RUN curl -L https://github.com/FStarLang/FStar/archive/refs/tags/v2024.01.13.tar.gz \
    --output Fstar.tar.gz
RUN tar --extract --file Fstar.tar.gz && rm -f Fstar.tar.gz && mv FStar-2024.01.13 fstar
RUN curl -L https://github.com/hacl-star/hacl-star/archive/refs/heads/main.zip \
    --output hacl-star.zip
RUN unzip hacl-star.zip && rm -rf hacl-star.zip && mv hacl-star-main/ hacl-star
RUN echo "FSTAR_HOME=~/fstar" >> $HOME/.bashrc \
         "HACL_HOME=~/hacl-star" >> $HOME/.bashrc \
         "HAX_HOME=~/hax" >> $HOME/.bashrc \
         "PATH=\"${PATH}:~/fstar/bin\"" >> $HOME/.bashrc
