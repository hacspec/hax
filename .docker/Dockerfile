# This Dockerfile should be run from the root directory of this repo
# e.g. `docker build -f .docker/Dockerfile . -t hax` from the parent directory

FROM ubuntu:24.04
LABEL maintainer="Franziskus Kiefer <franziskuskiefer@gmail.com>"

ENV SHELL /bin/bash
ENV USER hax-user
ENV LOGNAME $USER
ENV HOME /home/$USER
ENV LANG en_US.UTF-8
ENV LC_ALL $LANG
ENV PATH="$HOME/.cargo/bin:${PATH}"

# Install dependencies.
ADD .docker/setup.sh /tmp/setup.sh
RUN bash /tmp/setup.sh

WORKDIR $HOME
USER $USER
COPY --chown=hax-user:hax-user . $HOME/hax

# Setup & install.
ADD .docker/install.sh /tmp/install.sh
RUN bash /tmp/install.sh

# Start SSH (as root)
USER root
CMD ["/usr/sbin/sshd", "-D"]
