module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.Definitions.HilbertSymbols.PowerClassGroup
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Pairings on power classes
-/

namespace ClassFieldTheory

universe u

/-- Multiplicative pairings on `n`-th power classes with values in the
`n`-th roots of unity. -/
abbrev HilbertPairing (K : Type u) [Field K] (n : ℕ+) :=
  PowerClassGroup K n →*
    (PowerClassGroup K n →* rootsOfUnity (n : ℕ) K)

end ClassFieldTheory
