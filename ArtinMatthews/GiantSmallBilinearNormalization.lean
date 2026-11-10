module

public import ArtinMatthews.GiantSmallConditioningData
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ}

/-- The two original mass factors have their literal combined exponent. -/
theorem giantSmallMass_mul_tailMass (M ell : ℕ) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
        giantSmallTailMass P ell =
      ∏ j, (bandReciprocalMass (P j)) ^ (-(M : ℝ) - (ell : ℝ)) := by
  unfold markedPhysicalMass giantSmallTailMass
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [← pow_add]
  have hexp : -(M : ℝ) - (ell : ℝ) = -((M + ell : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]

/-- Squaring the actual conditioning normalization gives the original total mass. -/
theorem giantSmallConditioningNormalization_sq_product {k ell : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (giantSmallConditioningNormalization P k ell) ^ 2 =
      ∏ j, (bandReciprocalMass (P j)) ^ (-((k + ell : ℕ) : ℝ) - (ell : ℝ)) := by
  rw [giantSmallConditioningNormalization_sq hV, giantSmallMass_mul_tailMass]

/-- Zero extension retains both actual state conditions in a paired term. -/
theorem giantSmallStateValue_pair_eq {k ell : ℕ}
    (w₁ w₂ : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y y' : GiantTwoSidedFullResidue P)
    (a a' : MarkedPhysicalMarking P (k + ell)) (H : ℂ) :
    star (giantSmallStateValue w₁ y a) * H * giantSmallStateValue w₂ y' a' =
      if h : GiantSmallStateCondition y a then
        if h' : GiantSmallStateCondition y' a' then
          star (w₁ ⟨(y, a), h⟩) * H * w₂ ⟨(y', a'), h'⟩
        else 0
      else 0 := by
  classical
  unfold giantSmallStateValue
  split_ifs <;> simp

end
end ArtinMatthews
