FROM coqorg/coq:8.15.2-ocaml-4.14.0-flambda
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH $HOME/.cargo/bin:$PATH
RUN rustup update
RUN rustup toolchain install nightly-2022-07-04
RUN rustup component add --toolchain nightly-2022-07-04 rustc-dev llvm-tools-preview rust-analysis rust-src
RUN rustc --version
RUN cargo --version
RUN sudo apt-get update
RUN sudo apt-get install libppl-dev -y
RUN sudo apt-get install libmpfr-dev -y
RUN opam update
RUN opam switch create 4.12.0
RUN eval $(opam env --switch=4.12.0)
RUN opam config list; opam repo list; opam list
RUN opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
RUN opam update
RUN opam pin coq 8.15.2 -y
RUN eval $(opam env)
RUN git clone https://github.com/jasmin-lang/jasmin.git
RUN git clone https://github.com/SSProve/ssprove.git
RUN cd jasmin && git checkout 3d40bc89 && cd ..
RUN opam install -y --verbose ./jasmin/. --working-dir
RUN eval $(opam env)
RUN cd ssprove && git checkout jasmin && cd ..
RUN opam upgrade -y
RUN (opam install -y --verbose ./ssprove/ssprove.opam --working-dir) || echo "failed"
RUN cd ssprove && make -j7 && opam install -y --verbose ./ssprove.opam --working-dir --assume-built
