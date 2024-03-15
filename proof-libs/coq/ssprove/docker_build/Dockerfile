FROM mathcomp/mathcomp:2.1.0-coq-8.18
ENV PATH $HOME/.cargo/bin:$PATH
RUN opam config list; opam repo list; opam list
RUN opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
RUN opam update
RUN opam install .
