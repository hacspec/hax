#!/usr/bin/env bash

set -e

opam init --auto-setup --disable-sandboxing --yes --bare
opam switch create 4.14.1 --yes
eval $(opam env)

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain nightly-2022-12-06 -y
echo 'source $HOME/.cargo/env' >>$HOME/.bashrc
source "$HOME/.cargo/env"
git clone https://github.com/hacspec/hacspec-v2.git
cd hacspec-v2
git switch franziskus/container
sh ./setup.sh
