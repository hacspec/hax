# `ppx_generate_features`

Specific to `thir-elab`: 
    - generates a `FEATURES` module type;
    - modules `Off` and `On` of type `FEATURES`, one with every feature type set to `on`, the other with every feature type set to `off`;
    - a `SUBSET.T` module type that describe a subtyping relation between two modules of type `FEATURES`;
    - a `SUBSET.Id` module that maps every feature to themselves.
    
This PPX aims to alleviates the pain of adding new features.

