# An Unconditional Artin–Matthews Theorem for Simultaneous Primitive Roots

This repository contains the paper and the Lean formalization of Theorem 1.1.
The theorem gives a dyadic lower bound and positive lower relative prime density
when neither Matthews obstruction occurs. Either obstruction implies that the
set of simultaneous primitive primes is finite.

[Read the paper](An_Unconditional_Artin-Matthews_Theorem_for_Simultaneous_Primitive_Roots.pdf)

## Build

Install the Lean toolchain pinned in `lean-toolchain`, then run

```sh
lake exe cache get
lake build Solution
```

The checked endpoint is `ArtinMatthewsPaper.main_result` in `Solution.lean`.
`Challenge.lean` states the independent target for Comparator. The source and
dependency provenance is recorded in `formalization.yaml` and
`SOURCE_MANIFEST.json`.

The Lean code is released under Apache 2.0. See `PROVENANCE.md` for the paper
and third-party notices.
