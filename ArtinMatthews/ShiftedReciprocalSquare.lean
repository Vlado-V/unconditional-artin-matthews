module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A sharp reciprocal-scale sum bound by an elementary telescoping majorant. -/

noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem shifted_reciprocal_square_step (S : ℝ) (hS : 0 < S) (n : ℕ) :
    1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2 ≤
      S^2 / (S + n) - S^2 / (S + n + 1) := by
  have h0 : 0 < S + n := by positivity
  have h1 : 0 < S + n + 1 := by positivity
  calc
    _ = S^2 / (S + n + 1)^2 := by push_cast; field_simp; ring
    _ ≤ S^2 / ((S + n) * (S + n + 1)) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos h0 h1) (by nlinarith)
    _ = _ := by field_simp; ring

theorem shifted_reciprocal_square_partial (S : ℝ) (hS : 0 < S) (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) ≤
      S - S^2 / (S + N) := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, add_zero]
            have : S^2 / S = S := by field_simp
            rw [this, sub_self]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hstep := shifted_reciprocal_square_step S hS N
      push_cast at ih hstep ⊢
      simp only [add_assoc] at ih hstep ⊢
      linarith

theorem shifted_reciprocal_square_sum (S : ℝ) (hS : 0 < S) :
    Summable (fun n : ℕ => 1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) ∧
      (∑' n : ℕ, 1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) ≤ S := by
  have hb (N : ℕ) :
      (∑ n ∈ Finset.range N, 1 / (1 + ((n + 1 : ℕ) : ℝ) / S)^2) ≤ S :=
    (shifted_reciprocal_square_partial S hS N).trans (sub_le_self _ (by positivity))
  exact ⟨summable_of_sum_range_le (fun _ => by positivity) hb,
    Real.tsum_le_of_sum_range_le (fun _ => by positivity) hb⟩

end ArtinMatthews
