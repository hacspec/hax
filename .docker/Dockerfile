FROM nixpkgs/nix-flakes

RUN nix profile install github:hacspec/hacspec-v2#thir-export
RUN nix profile install github:hacspec/hacspec-v2#thir-elab
RUN nix profile install --priority 0 github:hacspec/hacspec-v2#circus
RUN cp ~/.nix-profile/bin/cargo-circus ~/.nix-profile/bin/circus
ENV PATH="$PATH:~/.nix-profile/bin"
