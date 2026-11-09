module

public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

/-! Balanced integer reductions used in the elementary generation of `Γ₁(3)`. -/

namespace ArtinMatthews

/-- Adding a suitable integer multiple of a nonzero integer leaves an absolute
remainder at most half the absolute modulus. -/
theorem exists_balanced_add_mul (a c : ℤ) (hc : c ≠ 0) :
    ∃ n : ℤ, 2 * |a + n * c| ≤ |c| := by
  let r : ℤ := round ((a : ℚ) / (c : ℚ))
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have h := mul_le_mul_of_nonneg_right
    (abs_sub_round ((a : ℚ) / (c : ℚ))) (abs_nonneg (c : ℚ))
  have heq : ((a : ℚ) / (c : ℚ) - (r : ℚ)) * (c : ℚ) =
      (a : ℚ) - (r : ℚ) * (c : ℚ) := by
    dsimp [r]
    field_simp
  change |(a : ℚ) / (c : ℚ) - (r : ℚ)| * |(c : ℚ)| ≤ _ at h
  rw [← abs_mul, heq] at h
  refine ⟨-r, ?_⟩
  have hcast : (2 : ℚ) * |((a + (-r) * c : ℤ) : ℚ)| ≤ |(c : ℚ)| := by
    push_cast
    have he : (a : ℚ) + -(r : ℚ) * (c : ℚ) =
        (a : ℚ) - (r : ℚ) * (c : ℚ) := by ring
    rw [he]
    linarith
  exact_mod_cast hcast

/-- The same reduction along multiples of `3a`. -/
theorem exists_three_balanced_add_mul (c a : ℤ) (ha : a ≠ 0) :
    ∃ n : ℤ, 2 * |c + 3 * n * a| ≤ 3 * |a| := by
  obtain ⟨n, hn⟩ := exists_balanced_add_mul c (3 * a) (mul_ne_zero (by norm_num) ha)
  refine ⟨n, ?_⟩
  calc
    2 * |c + 3 * n * a| = 2 * |c + n * (3 * a)| := by congr 2; ring
    _ ≤ |3 * a| := hn
    _ = 3 * |a| := by simp [abs_mul]

end ArtinMatthews
