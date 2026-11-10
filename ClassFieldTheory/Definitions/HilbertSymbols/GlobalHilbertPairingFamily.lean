module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairing
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Families of finite-place Hilbert pairings
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u

/-- A choice of power-class pairing on the completion of `F` at every finite
place.  No reciprocity law is hidden in this data type. -/
abbrev GlobalHilbertPairingFamily
    (F : Type u) [Field F] [NumberField F] (n : ℕ+) :=
  ∀ v : HeightOneSpectrum (𝓞 F), HilbertPairing (v.adicCompletion F) n

end ClassFieldTheory
