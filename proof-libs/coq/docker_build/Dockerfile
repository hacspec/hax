FROM coqorg/coq:8.16
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH $HOME/.cargo/bin:$PATH
RUN rustup update
RUN rustup toolchain install nightly-2022-07-04
RUN rustup component add --toolchain nightly-2022-07-04 rustc-dev llvm-tools-preview rust-analysis rust-src 
RUN rustc --version
RUN cargo --version
RUN opam config list; opam repo list; opam list
RUN opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
RUN opam update
RUN opam install coq-compcert coq-coqprime coq-quickchick --yes
