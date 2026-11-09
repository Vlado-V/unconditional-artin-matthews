module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingLaws
public import ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingNormResidueCriterion


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Local Hilbert pairings
-/

namespace ClassFieldTheory.HilbertPairing

universe u

/-- The algebraic laws and Kummer norm-residue criterion required of a local
Hilbert pairing.  These properties do not fix the value normalization of the
symbol; that requires a comparison with a normalized Artin map. -/
def IsLocalHilbertPairing
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  B.IsSteinberg ∧ B.IsSkewSymmetric ∧ B.IsNondegenerate ∧
    B.SatisfiesNormResidueCriterion

end ClassFieldTheory.HilbertPairing
