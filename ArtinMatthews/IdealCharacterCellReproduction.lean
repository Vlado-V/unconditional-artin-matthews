module

public import ArtinMatthews.IdealCharacterCellApply
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

/-! Retained cells reproduce every primitive character with the explicit
off-diagonal Gram error. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealCharacterCellApply_primitive_expansion (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (ψ : IdealPrimitiveCharacters Q) (x : IdealSelectedLabels P)
    (hr : ξ ≤ idealLogCellMass P h (idealLogCell h x)) :
    idealCharacterCellApply P Q h ξ
        (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x =
      ∑ χ : IdealPrimitiveCharacters Q,
        (idealLogCellMass P h (idealLogCell h x) : ℂ)⁻¹ *
          idealCharacterCellGram P Q h (idealLogCell h x) χ ψ *
            idealPrimitiveCharacterValue χ (idealSelectedProduct x) := by
  rw [idealCharacterCellApply_retained P Q h ξ _ x hr]
  unfold idealConditionalCharacterFrame idealFrameApply idealFrameSynthesis
  apply sum_congr rfl
  intro χ _
  congr 1
  unfold idealFrameCoefficient
  rw [idealCharacterCellGram, mul_sum]
  apply sum_congr rfl
  intro d _
  unfold idealCellConditionalMass
  split_ifs
  · rw [Complex.ofReal_div]
    ring
  · simp only [Complex.ofReal_zero, zero_mul, mul_zero]

theorem idealCharacterCellApply_primitive_error (P : I → Finset ℕ) (Q : ℕ) (h ξ : ℝ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hlarge : ∀ i p, p ∈ P i → Q < p)
    {ε : ℝ} (hε : 0 ≤ ε) (ψ : IdealPrimitiveCharacters Q) (x : IdealSelectedLabels P)
    (hm : 0 < idealLogCellMass P h (idealLogCell h x))
    (hr : ξ ≤ idealLogCellMass P h (idealLogCell h x))
    (hoff : ∀ χ : IdealPrimitiveCharacters Q, χ ≠ ψ →
      ‖idealCharacterCellGram P Q h (idealLogCell h x) χ ψ‖ ≤ ε) :
    ‖idealCharacterCellApply P Q h ξ
        (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x -
      idealPrimitiveCharacterValue ψ (idealSelectedProduct x)‖ ≤
        (Q : ℝ)^2 * (ε / idealLogCellMass P h (idealLogCell h x)) := by
  let v : IdealPrimitiveCharacters Q → ℂ := fun χ =>
    (idealLogCellMass P h (idealLogCell h x) : ℂ)⁻¹ *
      idealCharacterCellGram P Q h (idealLogCell h x) χ ψ *
        idealPrimitiveCharacterValue χ (idealSelectedProduct x)
  have hv : v ψ = idealPrimitiveCharacterValue ψ (idealSelectedProduct x) := by
    dsimp only [v]
    rw [idealCharacterCellGram_diag P Q h _ hP hlarge,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne'), one_mul]
  have he : idealCharacterCellApply P Q h ξ
        (fun d => idealPrimitiveCharacterValue ψ (idealSelectedProduct d)) x -
      idealPrimitiveCharacterValue ψ (idealSelectedProduct x) =
        ∑ χ ∈ (univ : Finset (IdealPrimitiveCharacters Q)).erase ψ, v χ := by
    rw [idealCharacterCellApply_primitive_expansion P Q h ξ ψ x hr]
    change (∑ χ, v χ) - _ = _
    rw [← sum_erase_add (s := univ) v (mem_univ ψ), hv, add_sub_cancel_right]
  rw [he]
  calc
    _ ≤ ∑ χ ∈ (univ : Finset (IdealPrimitiveCharacters Q)).erase ψ, ‖v χ‖ := norm_sum_le _ _
    _ ≤ ∑ _χ ∈ (univ : Finset (IdealPrimitiveCharacters Q)).erase ψ,
        ε / idealLogCellMass P h (idealLogCell h x) := by
      apply sum_le_sum
      intro χ hχ
      have hne : χ ≠ ψ := (mem_erase.mp hχ).1
      dsimp only [v]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
      calc
        _ ≤ ((idealLogCellMass P h (idealLogCell h x))⁻¹ * ε) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hoff χ hne) (by positivity))
            (idealPrimitiveCharacterValue_norm_le χ _) (norm_nonneg _) (by positivity)
        _ = _ := by ring
    _ ≤ (Q : ℝ)^2 * (ε / idealLogCellMass P h (idealLogCell h x)) := by
      rw [sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (div_nonneg hε hm.le)
      have hc : ((univ : Finset (IdealPrimitiveCharacters Q)).erase ψ).card ≤ Q^2 :=
        (card_erase_le).trans (by simpa only [card_univ] using idealPrimitiveCharacters_card_le Q)
      exact_mod_cast hc

end
end ArtinMatthews
