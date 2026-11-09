module

public import ArtinMatthews.MarkedMajorCharacterNorm
public import ArtinMatthews.MarkedMajorArcRoughLowBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine finite six-character cost is absorbed by a stronger instance
of the arbitrary-saving source estimate. -/
namespace ArtinMatthews
open Filter

 theorem markedMajor_character_cost {L a P Y X : ℝ} {q : ℕ}
    (hL : 0 < L) (hq : (q:ℝ) ≤ L^a) (hY : 0 ≤ Y) (hX : 0 ≤ X) :
    (q:ℝ)^6*((Y*X)*L^(-(P+6*a))) ≤ (Y*X)*L^(-P) := by
  have hq6 : (q:ℝ)^6 ≤ L^(6*a) := by
    calc
      _ ≤ (L^a)^6 := pow_le_pow_left₀ (Nat.cast_nonneg q) hq 6
      _ = L^(6*a) := by simpa only [Nat.cast_ofNat,mul_comm] using (Real.rpow_mul_natCast hL.le a 6).symm
  calc
    _ ≤ L^(6*a)*((Y*X)*L^(-(P+6*a))) :=
      mul_le_mul_of_nonneg_right hq6 (mul_nonneg (mul_nonneg hY hX) (Real.rpow_nonneg hL.le _))
    _ = (Y*X)*L^(-P) := by
      rw [mul_left_comm,← Real.rpow_add hL]
      congr 2
      ring

 theorem markedMajor_arc_unit_scale (a τ : ℝ) (hτ : 0 < τ) :
    ∀ᶠ L : ℝ in atTop, L^a ≤ Real.exp (L^(6/25:ℝ)) ∧
      Real.exp (L^(6/25:ℝ)) ≤ Real.exp (τ*L) := by
  filter_upwards [marked_polynomial_le_exp_rpow 1 a (6/25) (by norm_num),
    marked_rough_cutoff_scale (6/25) τ (by norm_num) hτ] with L hq hW
  exact ⟨by simpa only [one_mul] using hq,hW⟩

end ArtinMatthews
