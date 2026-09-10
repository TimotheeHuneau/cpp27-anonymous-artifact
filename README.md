# Installation

Run the following commands:

```
opam switch create . 5.4.0 --deps-only --repos=default,rocq-released=https://rocq-prover.org/opam/released
eval $(opam env)
make
```
