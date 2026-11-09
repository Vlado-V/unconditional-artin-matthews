module

public import ArtinMatthews.SpectralMixedCuspNormalization
public import ArtinMatthews.SpectralCuspEisensteinZeroRows


set_option backward.privateInPublic true
@[expose] public section

/-! The cusps in the shifted-correlation application are genuinely
inequivalent as soon as the left coprime factor exceeds one. -/

noncomputable section
open Matrix
open scoped MatrixGroups
namespace ArtinMatthews

theorem gamma0MixedCusps_inequivalent_of_one_lt (r s : ℕ) [NeZero s]
    (hr : 1 < r) :
    ¬ gamma0EisensteinCuspsEquivalent (r*s) (gamma0CuspOneOver s) 1 := by
  intro h
  obtain ⟨M, hC⟩ := (gamma0EisensteinCuspsEquivalent_iff (r*s) (gamma0CuspOneOver s) 1).mp h
  obtain ⟨k, hk⟩ := (gamma0MixedCuspCorrespondence_iff r s M.val).mp M.property
  rw [hC, zero_sub] at hk
  have hs : (s : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne s
  have hD : (r : ℤ) ∣ M.val 1 1 := by
    refine ⟨-k, ?_⟩
    apply mul_left_cancel₀ hs
    linear_combination -hk
  have hdet : M.val 0 0 * M.val 1 1 = 1 := by
    have h := M.val.property
    rwa [Matrix.det_fin_two, hC, mul_zero, sub_zero] at h
  have hd : (r : ℤ) ∣ 1 := hdet ▸ dvd_mul_of_dvd_right hD (M.val 0 0)
  have hd' : r ∣ 1 := by exact_mod_cast hd
  exact (not_le_of_gt hr) (Nat.le_of_dvd zero_lt_one hd')

end ArtinMatthews
