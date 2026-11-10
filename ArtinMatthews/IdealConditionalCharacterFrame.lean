module

public import ArtinMatthews.IdealCharacterCellGram
public import ArtinMatthews.IdealFiniteFrameOperator
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Conditional character Gram matrices use the literal cell mass.
The full frame norm follows from their derived row sums. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

def idealCellConditionalMass (P : I → Finset ℕ) (h : ℝ) (j : ℤ)
    (a : IdealSelectedLabels P) : ℝ :=
  if idealLogCell h a = j then idealSelectedMass P a / idealLogCellMass P h j else 0

def idealConditionalCharacterFrame (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (j : ℤ)
    (f : IdealSelectedLabels P → ℂ) : IdealSelectedLabels P → ℂ :=
  idealFrameApply (idealCellConditionalMass P h j)
    (fun χ : IdealPrimitiveCharacters Q =>
      fun a => idealPrimitiveCharacterValue χ (idealSelectedProduct a)) f

theorem idealCellConditionalMass_nonneg (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (h : ℝ) (j : ℤ)
    (a : IdealSelectedLabels P) : 0 ≤ idealCellConditionalMass P h j a := by
  unfold idealCellConditionalMass
  split_ifs
  · exact div_nonneg (idealSelectedMass_nonneg P hV a) (idealLogCellMass_nonneg P hV h j)
  · exact le_rfl

theorem idealCellConditionalMass_sum (P : I → Finset ℕ) (h : ℝ) (j : ℤ)
    (hm : 0 < idealLogCellMass P h j) :
    (∑ a, idealCellConditionalMass P h j a) = 1 := by
  have he : (∑ a, idealCellConditionalMass P h j a) =
      idealLogCellMass P h j / idealLogCellMass P h j := by
    rw [idealLogCellMass, sum_div]
    apply sum_congr rfl
    intro a _
    unfold idealCellConditionalMass
    split_ifs <;> first | rfl | simp only [zero_div]
  rw [he, div_self hm.ne']

theorem idealConditionalCharacterGram_eq (P : I → Finset ℕ) (Q : ℕ) (h : ℝ) (j : ℤ)
    (χ ψ : IdealPrimitiveCharacters Q) :
    idealFrameGram (idealCellConditionalMass P h j)
        (fun ρ : IdealPrimitiveCharacters Q =>
          fun a => idealPrimitiveCharacterValue ρ (idealSelectedProduct a)) χ ψ =
      (idealLogCellMass P h j : ℂ)⁻¹ * idealCharacterCellGram P Q h j ψ χ := by
  rw [idealFrameGram, idealCharacterCellGram, mul_sum]
  apply sum_congr rfl
  intro a _
  unfold idealCellConditionalMass
  split_ifs
  · rw [Complex.ofReal_div]
    ring
  · simp only [Complex.ofReal_zero, zero_mul, mul_zero]

theorem idealConditionalCharacterFrame_energy_le (P : I → Finset ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) (Q : ℕ) (h : ℝ) (j : ℤ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hlarge : ∀ i p, p ∈ P i → Q < p)
    {ε : ℝ} (hε : 0 ≤ ε) (hm : 0 < idealLogCellMass P h j)
    (hoff : ∀ χ ψ : IdealPrimitiveCharacters Q, χ ≠ ψ →
      ‖idealCharacterCellGram P Q h j χ ψ‖ ≤ ε)
    (f : IdealSelectedLabels P → ℂ) :
    idealFrameEnergy (idealCellConditionalMass P h j)
      (idealConditionalCharacterFrame P Q h j f) ≤
      (1 + (Q : ℝ)^2 * (ε / idealLogCellMass P h j))^2 *
        idealFrameEnergy (idealCellConditionalMass P h j) f := by
  apply idealFrameApply_energy_le _ (idealCellConditionalMass_nonneg P hV h j) _ (by positivity)
  intro χ
  calc
    _ ≤ ∑ ψ : IdealPrimitiveCharacters Q,
        ((if ψ = χ then (1 : ℝ) else 0) + ε / idealLogCellMass P h j) := by
      apply sum_le_sum
      intro ψ _
      rw [idealConditionalCharacterGram_eq]
      by_cases he : ψ = χ
      · subst ψ
        rw [idealCharacterCellGram_diag P Q h j hP hlarge,
          inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), norm_one]
        simp only [ite_true]
        exact le_add_of_nonneg_right (div_nonneg hε hm.le)
      · simp only [he, ite_false, zero_add, norm_mul, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hm]
        calc
          _ ≤ (idealLogCellMass P h j)⁻¹ * ε :=
            mul_le_mul_of_nonneg_left (hoff ψ χ he) (inv_nonneg.mpr hm.le)
          _ = _ := by ring
    _ = 1 + (Fintype.card (IdealPrimitiveCharacters Q) : ℝ) *
        (ε / idealLogCellMass P h j) := by
      rw [sum_add_distrib]
      simp only [sum_ite_eq', mem_univ, ite_true, sum_const, card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      have hcard : (Fintype.card (IdealPrimitiveCharacters Q) : ℝ) ≤ (Q : ℝ)^2 := by
        exact_mod_cast idealPrimitiveCharacters_card_le Q
      have hs := mul_le_mul_of_nonneg_right hcard (div_nonneg hε hm.le)
      linarith

end
end ArtinMatthews
