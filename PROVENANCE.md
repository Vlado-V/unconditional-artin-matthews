# Source provenance

The Apache-2.0 repository license covers the local Lean code. The accompanying paper is a separate work under its own terms.

Vendored source notices and license texts are retained in LICENSES. SOURCE_MANIFEST.json records the pinned upstream revisions and selected and packaged file digests. It also identifies the independent disk and real-pole replacements used in the OAI compatibility layer.

## Proof route

The formalization proves the statement of Theorem 1.1 in the accompanying paper. The Lean development uses the following intermediate arguments.

- The quadratic sieve uses positive-line principal contour remainders for both the original and the dual square weights. See [the original contour](ArtinMatthews/QuadraticHeckeSquareNormContour.lean) and [the dual contour](ArtinMatthews/QuadraticHeckeDualSquareContour.lean).
- The cubic weighted sieve uses the actual Euler correction's value and first derivative at 1 and a double-pole integral. These inputs suffice for the weighted bound. See [the Euler correction](ArtinMatthews/CubicSieveActualJointEuler.lean) and [the integral](ArtinMatthews/CubicSieveRetainedMain.lean).
- The symmetric probe uses the contraction factor `2 / (m + 1)`. Choosing `m` before the block length gives the required block decay. See [the probe bound](ArtinMatthews/IdealSymmetricProbe.lean) and [the parameter choice](ArtinMatthews/IdealProbeDecay.lean).
