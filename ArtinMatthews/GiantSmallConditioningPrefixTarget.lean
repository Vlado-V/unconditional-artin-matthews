module

public import ArtinMatthews.GiantSmallCanonicalPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A prefix-dependent target parameter, such as the translated
pending memory, is fixed on the actual zero-extended tail fiber. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

theorem giantSmallConditioningMap_prefix_target (q : ℝ)
    (d : MarkedPhysicalMarking P k)
    (w : MarkedPhysicalMarking P k → GiantTwoSidedResidueState P (k+ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) :
    giantSmallConditioningMap P k ell q d (fun t => w (giantSmallPrefix t.val.2) t) y =
      giantSmallConditioningMap P k ell q d (w d) y := by
  unfold giantSmallConditioningMap
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  unfold giantSmallStateValue
  by_cases h : GiantSmallStateCondition y (giantSmallAppend d r)
  · simp only [dite_eq_left h, giantSmallPrefix_append]
  · simp only [dite_eq_right h]

variable [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]

theorem giantSmallCanonicalPairing_eq_prefix_conditioned
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (q : ℝ)
    (w₁ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (w₂ : MarkedPhysicalMarking P k → GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : MarkedPhysicalMarking P k → GiantTwoSidedFullResidue P →
      GiantTwoSidedFullResidue P → ℂ) :
    giantSmallCanonicalPairing q w₁ (fun t => w₂ (giantSmallPrefix t.val.2) t) H =
      ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
        ∑ y' : GiantTwoSidedFullResidue P,
          ((Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ : ℂ) *
            star (giantSmallConditioningMap P k ell q d w₁ y) * H d y y' *
              giantSmallConditioningMap P k ell q d (w₂ d) y' := by
  rw [giantSmallCanonicalPairing_eq_conditioned hV]
  simp_rw [giantSmallConditioningMap_prefix_target]

end
end ArtinMatthews
