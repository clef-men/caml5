## Building

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The simplest way is to run the following command, which creates a local opam switch, installs dependencies and compiles Coq proofs:

```
make dist
```

Alternatively, you can directly install dependencies in the current opam switch and compile Coq proofs:

```
make depend
make
```
