module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
public import ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# A valuation-theoretic finite Galois form of Krasner's argument

For a finite Galois extension with a uniquely extended discrete valuation,
suppose `b` is closer to an integral element `a` than any nontrivial
automorphic displacement of `a`.  Then every automorphism fixing `b` also
fixes `a`.

This is the stabilizer step in Krasner's lemma.  Stating it directly for the
finite Galois overfield avoids introducing a second normed-field topology:
invariance of the normalized additive valuation and its ultrametric
inequality are sufficient.
-/

noncomputable section

universe u v w x

namespace RamificationTheory.HilbertRamification
namespace Higher

open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : DVF.{u, v} K} {target : DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- If `σ` fixes `b`, and `a-b` is strictly deeper than the displacement
`σ(a)-a` whenever that displacement is nonzero, then `σ` fixes `a`.

The proof is the elementary Krasner contradiction

`v(σ(a)-a) ≥ min(v(σ(a)-b), v(b-a)) = v(a-b)`.
-/
theorem valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close
    (huniq :
      RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension
        base target)
    (σ : Gal(L/K)) (a b : target.valuationSubring)
    (hfix :
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ b = b)
    (hclose :
      valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a ≠ a →
        IsDiscreteValuationRing.addVal target.valuationSubring
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) <
          IsDiscreteValuationRing.addVal target.valuationSubring
            (a - b)) :
    valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ a = a := by
  by_contra hne
  have hfirst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) =
        IsDiscreteValuationRing.addVal target.valuationSubring
          (a - b) := by
    calc
      IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) =
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ (a - b)) := by
              apply congrArg
                (IsDiscreteValuationRing.addVal
                  target.valuationSubring)
              rw [map_sub, hfix]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (a - b) :=
        addVal_valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ (a - b)
  have hsecond :
      IsDiscreteValuationRing.addVal target.valuationSubring (b - a) =
        IsDiscreteValuationRing.addVal target.valuationSubring (a - b) := by
    have hneg : b - a = -(a - b) := by ring
    rw [hneg,
      (IsDiscreteValuationRing.addVal target.valuationSubring).map_neg]
  have hultra :=
    IsDiscreteValuationRing.addVal_add
      (R := target.valuationSubring)
      (a :=
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - b)
      (b := b - a)
  have hle :
      IsDiscreteValuationRing.addVal target.valuationSubring (a - b) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a) := by
    have hsum :
        (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) +
            (b - a) =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a := by
      ring
    simpa [hfirst, hsecond, hsum] using hultra
  exact (not_le_of_gt (hclose hne)) hle

end Higher
end RamificationTheory.HilbertRamification

end
