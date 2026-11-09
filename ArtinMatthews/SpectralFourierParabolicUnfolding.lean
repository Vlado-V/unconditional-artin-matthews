module

public import ArtinMatthews.SpectralHorizontalLatticePartition
public import ArtinMatthews.SpectralCuspTranslationAdmissibility
public import ArtinMatthews.SpectralCuspFourierTestSeed


set_option backward.privateInPublic true
@[expose] public section

/-! Exact parabolic unfolding of the actual compact Fourier test.  The
translate step is N, and the Fourier phase is the existing frequency n/N. -/

noncomputable section
open Set
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

def cuspFourierWave (N : ℕ) (n : ℤ) (ρ : ℝ → ℝ) (z : UpperHalfPlane) : ℂ :=
  (ρ z.im : ℂ) * star (cuspFourierPhase (N : ℝ) n z.re)

theorem cuspFourierTestSeed_period_translate (N : ℕ) [NeZero N]
    (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (l : ℤ) (z : UpperHalfPlane) :
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpos).val
      (integerTranslation ((N : ℤ) * l) • z) =
        spectralHorizontalPartition (N : ℝ) (z.re + (N : ℝ) * l) • cuspFourierWave N n ρ z := by
  rw [cuspFourierTestSeed_apply, integerTranslation_eq_T_zpow,
    ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul]
  have hp := cuspFourierPhase_integer_shift_of_dvd N n ((N : ℤ) * l)
    (show (N : ℤ) ∣ n * ((N : ℤ) * l) from ⟨n*l,by ring⟩) z.re
  rw [hp]
  unfold cuspFourierWave
  simp only [Complex.real_smul, Complex.ofReal_mul, Int.cast_mul, Int.cast_natCast]
  ring

theorem cuspFourierTestSeed_parabolic_finsum (N : ℕ) [NeZero N]
    (n : ℤ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (∑ᶠ l : ℤ,
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n ρ hρ hcρ hpos).val
        (integerTranslation ((N : ℤ) * l) • z)) = cuspFourierWave N n ρ z := by
  simp_rw [cuspFourierTestSeed_period_translate]
  rw [← finsum_smul, spectralHorizontalPartition_lattice_finsum (Nat.cast_pos.mpr (NeZero.pos N)),
    one_smul]

theorem cuspFourierWave_translate_of_admissible (N : ℕ) [NeZero N]
    (n k : ℤ) (hNk : (N : ℤ) ∣ n*k) (ρ : ℝ → ℝ) (z : UpperHalfPlane) :
    cuspFourierWave N n ρ (integerTranslation k • z) = cuspFourierWave N n ρ z := by
  unfold cuspFourierWave
  rw [integerTranslation_eq_T_zpow, ModularGroup.re_T_zpow_smul, ModularGroup.im_T_zpow_smul,
    cuspFourierPhase_integer_shift_of_dvd N n k hNk]

end ArtinMatthews
