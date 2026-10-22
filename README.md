# Agda Portfolio — GovernorKaputula

Introductory examples of constructive proofs and dependently typed programming in Agda.

## Sample work

- **Logic:** swapping a product and composing constructive functions.
- **Arithmetic:** inductive proofs of right identity and associativity of addition.
- **Verified lists:** map preserves length and mapping identity returns the original list.
- **Dependent types:** length-indexed vectors, a head function requiring a nonempty vector, and a length-preserving vector map.

All examples are self-contained in `Portfolio.agda`, with no standard library dependency. The module uses `--safe --without-K`, contains no postulates or unfinished holes, and is checked by GitHub Actions.

## Check locally

With Agda installed, run:

```sh
agda --safe --without-K Portfolio.agda
```

The workflow installs `agda-bin` on Ubuntu 24.04 and runs the same check. See the Actions tab for the compiler result and version.
