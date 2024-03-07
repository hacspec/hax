#!/usr/bin/env bash

set -v -e -x

curl https://sh.rustup.rs -sSf | bash -s -- -y

# Prepare the sources
opam init --bare --disable-sandboxing
opam switch create 4.14.1
eval $(opam env)

OPAM_YES=true opam install --yes ocamlfind visitors menhir ppx_deriving_yojson sedlex wasm fix process pprint zarith yaml easy_logging terminal memtrace stdint batteries

# Install hax
cd $HOME/hax
./setup.sh -j 2
cd ~/

# Get F* and HACL* for running proofs
# curl -L https://github.com/FStarLang/FStar/releases/download/v2024.01.13/fstar_2024.01.13_Linux_x86_64.tar.gz \
#     --output Fstar.tar.gz
# tar --extract --file Fstar.tar.gz
curl -L https://github.com/FStarLang/FStar/archive/refs/tags/v2024.01.13.zip --output Fstar.zip
unzip Fstar.zip
rm -f Fstar.zip
mv FStar-2024.01.13 fstar
curl -L https://github.com/hacl-star/hacl-star/archive/refs/heads/main.zip \
    --output hacl-star.zip
unzip hacl-star.zip
rm -rf hacl-star.zip
mv hacl-star-main/ hacl-star
echo "export FSTAR_HOME=~/fstar" >>$HOME/.bashrc
echo "export HACL_HOME=~/hacl-star" >>$HOME/.bashrc
echo "export HAX_HOME=~/hax" >>$HOME/.bashrc
echo "export PATH=\"${PATH}:~/fstar/bin\"" >>$HOME/.bashrc
echo "alias fstar.exe='fstar.exe --z3version 4.8.12'" >>$HOME/.bashrc
echo "[[ ! -r /home/$USER/.opam/opam-init/init.sh ]] || source /home/$USER/.opam/opam-init/init.sh  > /dev/null 2> /dev/null" >>$HOME/.bashrc
