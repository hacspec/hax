FROM ubuntu:22.04

RUN apt update && apt upgrade -y && apt install -y git opam curl nodejs python2.7

RUN useradd -ms /bin/bash hacspec

USER hacspec
WORKDIR /home/hacspec

COPY setup.sh $HOME
RUN ./setup.sh
RUN rm setup.sh