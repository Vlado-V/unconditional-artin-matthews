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

/-! Two actual small states can be expanded into their literal ambient
residue and marking coordinates with both validity gates retained. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]

theorem giantSmallStateValue_double_sum
    (F : GiantTwoSidedResidueState P (k+ell) → GiantTwoSidedResidueState P (k+ell) → ℂ) :
    (∑ y : GiantTwoSidedFullResidue P, ∑ a : MarkedPhysicalMarking P (k+ell),
      ∑ y' : GiantTwoSidedFullResidue P, ∑ b : MarkedPhysicalMarking P (k+ell),
        giantSmallStateValue (fun s => giantSmallStateValue (F s) y' b) y a) =
      ∑ s : GiantTwoSidedResidueState P (k+ell), ∑ t : GiantTwoSidedResidueState P (k+ell), F s t := by
  have hinner (y : GiantTwoSidedFullResidue P) (a : MarkedPhysicalMarking P (k+ell)) :
      (∑ y' : GiantTwoSidedFullResidue P, ∑ b : MarkedPhysicalMarking P (k+ell),
        giantSmallStateValue (fun s => giantSmallStateValue (F s) y' b) y a) =
      giantSmallStateValue (fun s => ∑ t : GiantTwoSidedResidueState P (k+ell), F s t) y a := by
    by_cases h : GiantSmallStateCondition y a
    · simp only [giantSmallStateValue, dite_eq_left h]
      exact giantSmallStateValue_sum (F ⟨(y,a),h⟩)
    · simp only [giantSmallStateValue, dite_eq_right h, Finset.sum_const_zero]
  simp_rw [hinner]
  exact giantSmallStateValue_sum (fun s => ∑ t : GiantTwoSidedResidueState P (k+ell), F s t)

omit [DecidableEq J] [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val] in
theorem giantSmallStateValue_kernel
    (w₁ w₂ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : GiantTwoSidedFullResidue P → MarkedPhysicalMarking P (k+ell) →
      GiantTwoSidedFullResidue P → MarkedPhysicalMarking P (k+ell) → ℂ)
    (y y' : GiantTwoSidedFullResidue P) (a b : MarkedPhysicalMarking P (k+ell)) :
    giantSmallStateValue (fun s => giantSmallStateValue
      (fun t => star (w₁ s) * H s.val.1 s.val.2 t.val.1 t.val.2 * w₂ t) y' b) y a =
        star (giantSmallStateValue w₁ y a) * H y a y' b * giantSmallStateValue w₂ y' b := by
  by_cases h : GiantSmallStateCondition y a
  · by_cases h' : GiantSmallStateCondition y' b
    · simp only [giantSmallStateValue, dite_eq_left h, dite_eq_left h']
    · simp only [giantSmallStateValue, dite_eq_left h, dite_eq_right h', mul_zero]
  · simp only [giantSmallStateValue, dite_eq_right h, star_zero, zero_mul]

theorem giantSmallState_pairing_expand
    (w₁ w₂ : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (H : GiantTwoSidedFullResidue P → MarkedPhysicalMarking P (k+ell) →
      GiantTwoSidedFullResidue P → MarkedPhysicalMarking P (k+ell) → ℂ) :
    (∑ s : GiantTwoSidedResidueState P (k+ell), ∑ t : GiantTwoSidedResidueState P (k+ell),
      star (w₁ s) * H s.val.1 s.val.2 t.val.1 t.val.2 * w₂ t) =
      ∑ y : GiantTwoSidedFullResidue P, ∑ a : MarkedPhysicalMarking P (k+ell),
        ∑ y' : GiantTwoSidedFullResidue P, ∑ b : MarkedPhysicalMarking P (k+ell),
          star (giantSmallStateValue w₁ y a) * H y a y' b * giantSmallStateValue w₂ y' b := by
  rw [← giantSmallStateValue_double_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y' _
  apply Finset.sum_congr rfl
  intro b _
  exact giantSmallStateValue_kernel w₁ w₂ H y y' a b

end
end ArtinMatthews
