module

public import ArtinMatthews.GiantComparisonStripLabels
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

/-! The reciprocal of the copied product converts its ordered labels to
their harmonic probability law, leaving one fresh mass for each endpoint. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k : ℕ}
  {C : J → Finset (Fin k)}

def giantComparisonSharedMass (c : GiantComparisonSharedLabels P C) : ℝ :=
  giantTwoSidedPatternAuxiliaryMass (C := fun j => univ \ C j) c

theorem giantComparisonSharedMass_sum [DecidableEq J]
    (C : J → Finset (Fin k)) (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ c : GiantComparisonSharedLabels P C, giantComparisonSharedMass c) = 1 :=
  giantTwoSidedPatternAuxiliaryMass_sum (fun j => univ \ C j) hV

theorem giantComparisonSlotCard (C : Finset (Fin k)) (ell : ℕ) :
    (univ \ C).card + (ell+C.card) = k+ell := by
  have hc : C.card ≤ k := by
    simpa only [card_univ, Fintype.card_fin] using card_le_card (subset_univ C)
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  omega

theorem giantComparisonSharedMass_eq_div (c : GiantComparisonSharedLabels P C) :
    giantComparisonSharedMass c =
      (∏ j, (bandReciprocalMass (P j))⁻¹^(univ \ C j).card) /
        (giantComparisonSharedProduct c : ℝ) := by
  unfold giantComparisonSharedMass giantTwoSidedPatternAuxiliaryMass giantComparisonSharedProduct
  rw [Nat.cast_prod, ← prod_div_distrib]
  apply prod_congr rfl
  intro j _
  rw [Nat.cast_prod]
  simp only [markedHarmonicAtom, div_eq_mul_inv, one_mul, prod_mul_distrib,
    prod_inv_distrib, prod_const, card_univ, Fintype.card_coe]
  ring

theorem giantComparisonStrip_mass_factor (C : J → Finset (Fin k)) (ell : ℕ)
    (c : GiantComparisonSharedLabels P C) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) *
        giantTwoSidedPatternFreshMass P C ell / (giantComparisonSharedProduct c : ℝ) =
      giantComparisonSharedMass c * giantTwoSidedPatternFreshMass P C ell^2 := by
  have hσ : markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) =
      (∏ j, (bandReciprocalMass (P j))⁻¹^(univ \ C j).card) *
        giantTwoSidedPatternFreshMass P C ell := by
    unfold markedPhysicalMass giantTwoSidedPatternFreshMass
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro j _
    rw [← pow_add, giantComparisonSlotCard]
  rw [hσ, giantComparisonSharedMass_eq_div]
  ring

end
end ArtinMatthews
