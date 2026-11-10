module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.Definitions.HilbertSymbols.GlobalInfinitePlaceHilbertSymbol
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceFiniteSupport
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.HilbertProductFormula
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Mathlib-facing Hilbert product formula

The established product formula is transported from the internal subgroup of
roots of unity to Mathlib's `rootsOfUnity`.
-/

noncomputable section

namespace ClassFieldTheory

open scoped BigOperators Classical NumberField
open NumberField IsDedekindDomain

/-- The finite-place Hilbert factor, transported from the internal
unit-root subgroup to Mathlib's `rootsOfUnity`. -/
noncomputable def globalFinitePlaceHilbertSymbol
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    rootsOfUnity (n : ℕ) F :=
  (KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ))
    (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
      F n hnF hmu v a b)

/-- **Hilbert product formula.**  The product of the local symbols of two
global units over every finite and infinite place is one. -/
theorem hilbertProductFormula
    (F : Type) [Field F] [NumberField F]
    (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (a b : Fˣ) :
    (∏ v : InfinitePlace F,
        globalInfinitePlaceHilbertSymbol F n v a b) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        globalFinitePlaceHilbertSymbol F n hnF hmu v a b = 1 := by
  let e := KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
  have hfinite :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol_hasFiniteMulSupport
      F n hnF hmu a b
  change
    (∏ v : InfinitePlace F,
        e (GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol
          F n v a b)) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F),
        e (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
          F n hnF hmu v a b) = 1
  calc
    _ = e
        ((∏ v : InfinitePlace F,
            GlobalClassFieldTheory.Reciprocity.infinitePlaceHilbertSymbol
              F n v a b) *
          ∏ᶠ v : HeightOneSpectrum (𝓞 F),
            GlobalClassFieldTheory.Reciprocity.finitePlaceHilbertSymbol
              F n hnF hmu v a b) := by
      rw [map_mul, map_prod, map_finprod e hfinite]
    _ = e 1 := congrArg e
      (GlobalClassFieldTheory.Reciprocity.hilbertSymbol_allPlaces_product_eq_one
        F n hnF hmu a b)
    _ = 1 := map_one e

end ClassFieldTheory
