module

public import ArtinMatthews.MarkedMinorArcDirtySeparation
public import Mathlib.Analysis.SpecificLimits.Normed


set_option backward.privateInPublic true
@[expose] public section

/-! Actual repeated pending-index choices are absorbed by the retained
outgoing damping, with no distinct-numeric-value or anchor assumption. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Uniform source index damping for every 0≤rho<1, including n=0. -/
theorem markedMinorDirty_index_damping {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (n : ℕ) :
    (n : ℝ)*ρ^(n-1) ≤ 1/(1-ρ)^2 := by
  cases n with
  | zero => simp only [Nat.cast_zero,zero_mul]; positivity
  | succ n =>
    have hs := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := ρ) 1
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg hρ₀] using hρ₁)
    have hb := sum_le_hasSum ({n} : Finset ℕ) (fun m _ => by positivity) hs
    simpa only [Finset.sum_singleton,Nat.choose_one_right,Nat.cast_add,Nat.cast_one,
      Nat.add_sub_cancel,Nat.reduceAdd] using hb

/-- Selecting one eligible pending index and damping all the other hits is
bounded uniformly even when numeric labels and anchors repeat. -/
theorem markedMinorDirty_pending_choices {ι : Type*} (H : Finset ι)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    (∑ _j ∈ H, ρ^(H.card-1)) ≤ 1/(1-ρ)^2 := by
  simpa only [Finset.sum_const,smul_eq_mul,nsmul_eq_mul] using
    markedMinorDirty_index_damping hρ₀ hρ₁ H.card

/-- Newly stored hits only decrease the genuine damping factor. -/
theorem markedMinorDirty_pending_choices_extra {ι : Type*} (H : Finset ι)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (k : ℕ) :
    (∑ _j ∈ H, ρ^(H.card-1+k)) ≤ 1/(1-ρ)^2 := by
  calc
    _ = (∑ _j ∈ H, ρ^(H.card-1))*ρ^k := by simp only [pow_add,Finset.sum_mul]
    _ ≤ (∑ _j ∈ H, ρ^(H.card-1))*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ hρ₀ hρ₁.le) (Finset.sum_nonneg (fun _ _ => pow_nonneg hρ₀ _))
    _ = ∑ _j ∈ H, ρ^(H.card-1) := mul_one _
    _ ≤ _ := markedMinorDirty_pending_choices H hρ₀ hρ₁

end ArtinMatthews
