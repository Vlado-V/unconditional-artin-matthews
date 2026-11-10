module

public import ArtinMatthews.GiantSmallConditioningData
public import ArtinMatthews.GiantSmallConditioningBudget
public import ArtinMatthews.GiantTwoSidedResidueInitialMass
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Cauchy in the actual tail fibers and exact prefix/tail disintegration
give the small-map estimate in its original two finite Haar measures. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ} {k ell : ℕ}

private theorem norm_sum_sq_le_card {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ a ∈ s, f a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a ∈ s, ‖f a‖ ^ 2 := by
  calc
    _ ≤ (∑ a ∈ s, ‖f a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
    _ ≤ _ := by
      simpa using sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => ‖f a‖)

omit [DecidableEq J] in
theorem giantSmallStateValue_norm_sq
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) (a : MarkedPhysicalMarking P (k + ell)) :
    ‖giantSmallStateValue w y a‖ ^ 2 =
      giantSmallStateValue (fun s => ‖w s‖ ^ 2) y a := by
  unfold giantSmallStateValue
  split_ifs <;> simp

theorem giantSmallConditioning_sum_tail
    {E : Type*} [AddCommMonoid E] (w : GiantTwoSidedResidueState P (k + ell) → E)
    (y : GiantTwoSidedFullResidue P) (d : MarkedPhysicalMarking P k) :
    (∑ r : MarkedPhysicalMarking P ell, giantSmallStateValue w y (giantSmallAppend d r)) =
      ∑ r ∈ giantSmallConditioningTails (ell := ell) y d, giantSmallStateValue w y (giantSmallAppend d r) := by
  rw [giantSmallConditioningTails, sum_filter]
  apply sum_congr rfl
  intro r _
  by_cases h : GiantSmallStateCondition y (giantSmallAppend d r)
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact dite_eq_right h

theorem giantSmallConditioning_tail_cauchy
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) (d : MarkedPhysicalMarking P k) :
    ‖∑ r : MarkedPhysicalMarking P ell, giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2 ≤
      ((giantSmallConditioningTails (ell := ell) y d).card : ℝ) *
        ∑ r : MarkedPhysicalMarking P ell, ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2 := by
  rw [giantSmallConditioning_sum_tail]
  apply (norm_sum_sq_le_card _ _).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)

theorem giantSmallConditioningMap_pointwise
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) {q B : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (P j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B)
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ)
    (y : GiantTwoSidedFullResidue P) (d : MarkedPhysicalMarking P k) :
    ‖giantSmallConditioningMap P k ell q d w y‖ ^ 2 ≤
      (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
        B ^ Fintype.card J) *
          ∑ r : MarkedPhysicalMarking P ell, ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2 := by
  let A := giantSmallConditioningNormalization P k ell
  let D := giantTwoSidedResidueDamping P (k + ell) q y
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell)
  let c := ((giantSmallConditioningTails (ell := ell) y d).card : ℝ)
  have hA : 0 ≤ A := giantSmallConditioningNormalization_nonneg (fun j => (hV j).le)
  have hD : D ∈ Set.Icc (0 : ℝ) 1 :=
    giantTwoSidedResidueDamping_mem_unitInterval P (k + ell) ⟨hq.le, hq1⟩ y
  have hσ : 0 ≤ σ := prod_nonneg fun j _ => pow_nonneg (inv_nonneg.mpr (hV j).le) _
  have hcoef : A ^ 2 * D ^ 2 * c ≤ σ * B ^ Fintype.card J := by
    calc
      _ = σ * ((c * giantSmallTailMass P ell * D) * D) := by
        dsimp only [A]
        rw [giantSmallConditioningNormalization_sq hV]
        ring
      _ ≤ σ * ((B ^ Fintype.card J) * D) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (giantSmallConditioningTails_budget hP hdis hV hq hB hbudget y d) hD.1) hσ
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hB _) hD.2) hσ
  unfold giantSmallConditioningMap
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hA, abs_of_nonneg hD.1,
    mul_pow, mul_pow]
  calc
    _ ≤ (A ^ 2 * D ^ 2) * (c *
        ∑ r : MarkedPhysicalMarking P ell, ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (giantSmallConditioning_tail_cauchy w y d)
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (A ^ 2 * D ^ 2 * c) *
        ∑ r : MarkedPhysicalMarking P ell, ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sum_nonneg fun _ _ => sq_nonneg _)

theorem giantSmallConditioning_norm_sum
    [∀ p : ↥(markedPhysicalBandPrimes P), NeZero p.val]
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) {q B : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B)
    (hbudget : ∀ j (z : ℕ),
      (bandReciprocalMass (P j))⁻¹ ^ ell * ((z : ℝ) + (ell : ℝ)) ^ ell *
        q ^ ((z : ℝ) / 2) ≤ B)
    (w : GiantTwoSidedResidueState P (k + ell) → ℂ) :
    (∑ d : MarkedPhysicalMarking P k,
      giantSmallResidueEnergy (giantSmallConditioningMap P k ell q d w)) ≤
      B ^ Fintype.card J * giantSmallStateEnergy w := by
  have hpartition : (∑ d : MarkedPhysicalMarking P k,
      ∑ y : GiantTwoSidedFullResidue P, ∑ r : MarkedPhysicalMarking P ell,
        ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2) =
      ∑ s : GiantTwoSidedResidueState P (k + ell), ‖w s‖ ^ 2 := by
    simp_rw [giantSmallStateValue_norm_sq]
    rw [sum_comm]
    simp_rw [giantSmallAppend_sum]
    exact giantSmallStateValue_sum (fun s => ‖w s‖ ^ 2)
  unfold giantSmallResidueEnergy giantSmallStateEnergy
  rw [← mul_sum]
  calc
    _ ≤ (Fintype.card (GiantTwoSidedFullResidue P) : ℝ)⁻¹ *
        ∑ d : MarkedPhysicalMarking P k, ∑ y : GiantTwoSidedFullResidue P,
          (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k + ell) *
            B ^ Fintype.card J) *
            ∑ r : MarkedPhysicalMarking P ell, ‖giantSmallStateValue w y (giantSmallAppend d r)‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact sum_le_sum fun d _ => sum_le_sum fun y _ =>
        giantSmallConditioningMap_pointwise hP hdis hV hq hq1 hB hbudget w y d
    _ = _ := by
      simp_rw [← mul_sum]
      rw [hpartition, giantTwoSidedResidueHaarStateMass_eq]
      ring

end
end ArtinMatthews
