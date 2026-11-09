module

public import ArtinMatthews.SpectralGammaThreeQuarterStrip
public import ArtinMatthews.SpectralGammaStripBound


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem spectral_weyl_gamma_pair_closed_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t y : ℝ, 0 ≤ y → y ≤ 5/8 →
      ‖spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I) /
        Complex.Gamma (1-2*I*((t : ℂ)+(y : ℂ)*I))‖ ≤ C*(1+t^2)^3 := by
  obtain ⟨G, hG, hg⟩ := spectralABLCoshCancellation_exp_strip_bound
  obtain ⟨D, hD, hd⟩ := spectral_inv_gamma_closed_strip_bound (7/4) (by norm_num)
  refine ⟨2*G*D, by positivity, ?_⟩
  intro t y hy0 hy1
  have hy : |y| ≤ 3/4 := by rw [abs_of_nonneg hy0]; linarith
  have hp := hg t y hy
  have hq := hd (1/2+2*y) (-2*t) (by linarith) (by linarith)
  have harg : (((1/2+2*y+1/2 : ℝ) : ℂ)+((-2*t : ℝ) : ℂ)*I) =
      1-2*I*((t : ℂ)+(y : ℂ)*I) := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  rw [harg, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ)<2)] at hq
  have he : Real.pi*(2*|t|)/2 = Real.pi*|t| := by ring
  rw [he] at hq
  have hpoly : 1+2*|t| ≤ 2*(1+t^2) := by nlinarith [sq_abs t, sq_nonneg (|t|-1)]
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ ‖spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I)‖ *
        (D*(1+2*|t|)*Real.exp (Real.pi*|t|)) :=
      mul_le_mul_of_nonneg_left hq (norm_nonneg _)
    _ = D*(1+2*|t|)*(Real.exp (Real.pi*|t|)*
        ‖spectralABLCoshCancellation ((t : ℂ)+(y : ℂ)*I)‖) := by ring
    _ ≤ D*(1+2*|t|)*(G*(1+t^2)^2) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ D*(2*(1+t^2))*(G*(1+t^2)^2) := by gcongr
    _ = _ := by ring

end
end ArtinMatthews
