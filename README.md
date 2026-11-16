# Installation

Run the following commands:

```
opam switch create . 5.4.0 --deps-only --repos=default,rocq-released=https://rocq-prover.org/opam/released
eval $(opam env)
make
```

Our proof is contained in the `DLS` folder.

Material in the `Core` file is from the first-order logic library, trimmed to quicken compilation time the the bare necessity.