module

public import ArtinMatthews.SpectralKLGaussianData
public import ArtinMatthews.SpectralKLDirectDefinitions


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped ContDiff ComplexConjugate
noncomputable section

def spectralKLGaussianWeightedData (h : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  h z * spectralKLGaussianData R z

theorem spectralKLGaussianData_direct_rapid (R : ℝ) (hR : 0 < R) :
    SpectralKLDirectStripRapid (spectralKLGaussianData R) := by
  intro N
  simpa only [div_mul_eq_mul_div] using
    spectralKLGaussianData_strip_rapid R hR (Real.pi / 2) (3 / 4) (by norm_num) N

theorem spectralKLGaussianWeightedData_direct_rapid (h : ℂ → ℂ) (R : ℝ) (hR : 0 < R)
    (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ t y : ℝ, |y| ≤ 3 / 4 → ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H) :
    SpectralKLDirectStripRapid (spectralKLGaussianWeightedData h R) := by
  intro N
  obtain ⟨C, hC, hb⟩ := spectralKLGaussianData_direct_rapid R hR N
  refine ⟨H * C, mul_nonneg hH hC, ?_⟩
  intro t y hy
  rw [spectralKLGaussianWeightedData, norm_mul]
  calc
    _ = ‖h ((t : ℂ) + (y : ℂ) * I)‖ *
        ((1 + t ^ 2) ^ N * Real.exp (Real.pi * |t| / 2) *
          ‖spectralKLGaussianData R ((t : ℂ) + (y : ℂ) * I)‖) := by ring
    _ ≤ _ := mul_le_mul (hh t y hy) (hb t y hy) (by positivity) hH

theorem spectralKLGaussianWeightedData_differentiableAt (h : ℂ → ℂ) (R : ℝ)
    (z : ℂ) (hh : DifferentiableAt ℂ h z) :
    DifferentiableAt ℂ (spectralKLGaussianWeightedData h R) z :=
  hh.mul ((spectralKLGaussianData_differentiable R) z)

theorem spectralKLGaussianWeightedData_real_contDiff (h : ℂ → ℂ) (R : ℝ)
    (hh : ContDiff ℝ ∞ (fun t : ℝ => h (t : ℂ))) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralKLGaussianWeightedData h R (t : ℂ)) :=
  hh.mul (spectralKLGaussianData_real_contDiff R)

theorem spectralKLGaussianWeightedData_even (h : ℂ → ℂ) (R : ℝ)
    (hh : ∀ z : ℂ, h (-z) = h z) (z : ℂ) :
    spectralKLGaussianWeightedData h R (-z) = spectralKLGaussianWeightedData h R z := by
  rw [spectralKLGaussianWeightedData, spectralKLGaussianWeightedData, hh, spectralKLGaussianData_even]

theorem spectralKLGaussianData_real_star (R t : ℝ) :
    star (spectralKLGaussianData R (t : ℂ)) = spectralKLGaussianData R (t : ℂ) := by
  rw [spectralKLGaussianData_real]
  change conj ((Real.exp (-((t / R) ^ 2)) : ℝ) : ℂ) = _
  exact conj_ofReal _

theorem spectralKLGaussianWeightedData_real_star (h : ℂ → ℂ) (R : ℝ)
    (hh : ∀ t : ℝ, star (h (t : ℂ)) = h (t : ℂ)) (t : ℝ) :
    star (spectralKLGaussianWeightedData h R (t : ℂ)) =
      spectralKLGaussianWeightedData h R (t : ℂ) := by
  rw [spectralKLGaussianWeightedData, star_mul', hh, spectralKLGaussianData_real_star]

theorem spectralKLGaussianData_order (R : ℝ) (ν : ℂ) :
    spectralKLGaussianData R (-I * ν) = Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  unfold spectralKLGaussianData
  congr 1
  rw [div_pow, mul_pow, neg_sq, I_sq]
  ring


theorem spectralKLGaussianData_strip_uniform (R : ℝ) (hR : 1 ≤ R)
    (t y : ℝ) (hy : |y| ≤ 3 / 4) :
    ‖spectralKLGaussianData R ((t : ℂ) + (y : ℂ) * I)‖ ≤ Real.exp (9 / 16 : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hy2 : y ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr hy
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  have hquot : y ^ 2 / R ^ 2 ≤ (9 / 16 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hR0)).mpr
    nlinarith
  rw [spectralKLGaussianData_norm_shift]
  apply Real.exp_le_exp.mpr
  rw [div_pow]
  nlinarith [sq_nonneg (t / R)]

theorem spectralKLGaussianWeightedData_strip_uniform (h : ℂ → ℂ) (R : ℝ) (hR : 1 ≤ R)
    (H : ℝ) (hH : 0 ≤ H)
    (hh : ∀ t y : ℝ, |y| ≤ 3 / 4 → ‖h ((t : ℂ) + (y : ℂ) * I)‖ ≤ H)
    (t y : ℝ) (hy : |y| ≤ 3 / 4) :
    ‖spectralKLGaussianWeightedData h R ((t : ℂ) + (y : ℂ) * I)‖ ≤ H * Real.exp (9 / 16 : ℝ) := by
  rw [spectralKLGaussianWeightedData, norm_mul]
  exact mul_le_mul (hh t y hy) (spectralKLGaussianData_strip_uniform R hR t y hy)
    (norm_nonneg _) hH

end
end ArtinMatthews
