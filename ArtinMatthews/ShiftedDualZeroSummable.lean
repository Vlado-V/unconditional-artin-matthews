module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.ShiftedDualZeroEnergy
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.MeasureTheory.Covering.Besicovitch
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

/-! Absolute summability of the genuine zero-frequency fiber follows from
square summability, without a divisor or modulus multiplicity. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

def shiftedDualZeroMajorant (m3 m4 : ℕ) (a b : ℕ → ℂ) (k : ℕ × ℕ) : ℝ :=
  if m4 * k.2 = m3 * k.1 then ‖a k.1 * b k.2‖ else 0

theorem shiftedDualZeroMajorant_nonneg (m3 m4 : ℕ) (a b : ℕ → ℂ) (k : ℕ × ℕ) :
    0 ≤ shiftedDualZeroMajorant m3 m4 a b k := by
  unfold shiftedDualZeroMajorant
  split_ifs <;> positivity

theorem shiftedDualZeroMajorant_finite (m3 m4 : ℕ) (hm3 : 0 < m3) (hm4 : 0 < m4)
    (a b : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖^2))
    (hb : Summable (fun n => ‖b n‖^2)) (u : Finset (ℕ × ℕ)) :
    (∑ k ∈ u, shiftedDualZeroMajorant m3 m4 a b k) ≤
      ((∑' n, ‖a n‖^2) + (∑' n, ‖b n‖^2)) / 2 := by
  classical
  let S := u.image Prod.fst
  let T := u.image Prod.snd
  let P := shiftedDualZeroPairs S T m3 m4
  have hsub : u.filter (fun k => m4 * k.2 = m3 * k.1) ⊆ P := by
    intro k hk
    obtain ⟨hku, hke⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem Prod.fst hku, Finset.mem_image_of_mem Prod.snd hku⟩, hke⟩
  have hfst : (∑ k ∈ P, ‖a k.1‖^2) ≤ ∑' n, ‖a n‖^2 := by
    dsimp only [P]
    rw [← Finset.sum_image (f := fun n : ℕ => ‖a n‖^2)
      (shiftedDualZeroPairs_fst_injective S T m3 m4 hm4)]
    exact ha.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hsnd : (∑ k ∈ P, ‖b k.2‖^2) ≤ ∑' n, ‖b n‖^2 := by
    dsimp only [P]
    rw [← Finset.sum_image (f := fun n : ℕ => ‖b n‖^2)
      (shiftedDualZeroPairs_snd_injective S T m3 m4 hm3)]
    exact hb.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  calc
    _ = ∑ k ∈ u.filter (fun k => m4 * k.2 = m3 * k.1), ‖a k.1 * b k.2‖ := by
      simp only [shiftedDualZeroMajorant, Finset.sum_filter]
    _ ≤ ∑ k ∈ P, ‖a k.1 * b k.2‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ k ∈ P, (‖a k.1‖^2 + ‖b k.2‖^2) / 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      nlinarith [sq_nonneg (‖a k.1‖ - ‖b k.2‖)]
    _ = ((∑ k ∈ P, ‖a k.1‖^2) + (∑ k ∈ P, ‖b k.2‖^2)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

theorem shiftedDualZeroMajorant_summable (m3 m4 : ℕ) (hm3 : 0 < m3) (hm4 : 0 < m4)
    (a b : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖^2))
    (hb : Summable (fun n => ‖b n‖^2)) :
    Summable (shiftedDualZeroMajorant m3 m4 a b) ∧
      (∑' k, shiftedDualZeroMajorant m3 m4 a b k) ≤
        ((∑' n, ‖a n‖^2) + (∑' n, ‖b n‖^2)) / 2 := by
  have h0 := shiftedDualZeroMajorant_nonneg m3 m4 a b
  have hbound := shiftedDualZeroMajorant_finite m3 m4 hm3 hm4 a b ha hb
  exact ⟨summable_of_sum_le h0 hbound, Real.tsum_le_of_sum_le h0 hbound⟩

end ArtinMatthews
