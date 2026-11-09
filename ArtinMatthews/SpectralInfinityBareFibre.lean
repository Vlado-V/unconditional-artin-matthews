module

public import ArtinMatthews.SpectralABLSameCuspAtkinLehner
public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralInfinityKloostermanWeil


set_option backward.privateInPublic true
@[expose] public section

/-! The actual identity cusp and the actual 1/N cusp give the same
diagonal bare geometric fibre at each positive raw modulus. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

private theorem infinity_diagonalKloosterman_eq_oneOver (N c : ℕ) [NeZero N] [NeZero c]
    (n : ℤ) : gamma0TrueWidthKloostermanSum N 1 1 c n n =
      gamma0TrueWidthKloostermanSum N (gamma0CuspOneOver N) (gamma0CuspOneOver N) c n n := by
  by_cases hc : N ∣ c
  · obtain ⟨d, rfl⟩ := hc
    have hd : d ≠ 0 := fun h => NeZero.ne (N*d) (by rw [h, Nat.mul_zero])
    let _ : NeZero d := ⟨hd⟩
    rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_left (dvd_mul_right N d)]
    simpa only [one_mul] using
      (gamma0MixedSameCuspKloosterman_diag_eq_standard 1 N d (Nat.coprime_one_left N) n).symm
  · rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_right hc]
    simpa only [one_mul] using
      (gamma0MixedSameCuspKloosterman_zero_of_not_dvd 1 N c hc n n).symm

theorem gamma0Infinity_bareFibre_eq_oneOver (N : ℕ) [NeZero N]
    (c : Ioi (0 : ℕ)) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre N 1 1 c n n H =
      gamma0TrueWidthBareFibre N (gamma0CuspOneOver N) (gamma0CuspOneOver N) c n n H := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hinfty : gamma0TrueWidthModulus N 1 1 (c.val : ℝ) = (c.val : ℝ) := by
    simp [gamma0TrueWidthModulus, gamma0CuspTrueWidth_identity]
  have honeOver : gamma0TrueWidthModulus N (gamma0CuspOneOver N) (gamma0CuspOneOver N)
      (c.val : ℝ) = (c.val : ℝ) := by
    simpa only [one_mul] using gamma0AtkinSameCusp_modulus 1 N c.val (Nat.coprime_one_left N)
  unfold gamma0TrueWidthBareFibre
  dsimp only
  rw [hinfty, honeOver, infinity_diagonalKloosterman_eq_oneOver N c.val n]

theorem gamma0Infinity_bareFibre_zero (N : ℕ) [NeZero N] (c : Ioi (0 : ℕ))
    (hc : ¬ N ∣ c.val) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre N 1 1 c n n H = 0 := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  simp only [gamma0TrueWidthBareFibre, gamma0TrueWidthKloostermanSum_identity_eq_standard,
    ite_eq_right hc, zero_mul]

end ArtinMatthews
