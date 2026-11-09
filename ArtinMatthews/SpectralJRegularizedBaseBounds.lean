module

public import ArtinMatthews.SpectralJRegularizedWeightBounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set Complex
open scoped ContDiff
noncomputable section

def spectralJRegularizedBase (f : ℝ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  (Real.pi : ℂ) * spectralJForwardTransform f z *
    spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)

theorem spectralJRegularizedWeight_factor (f : ℝ → ℂ) (L : ℝ) (z : ℂ) :
    spectralJRegularizedWeight f L z = spectralJRegularizedBase f L z * spectralABLCoshCancellation z := by
  unfold spectralJRegularizedWeight spectralJRegularizedBase
  ring

private theorem spectralJRegularizedBase_bound (f : ℝ → ℂ) (L A U t y : ℝ)
    (hA : 0 ≤ A) (hU : 0 ≤ U)
    (hb : ‖spectralJForwardTransform f ((t : ℂ) + (y : ℂ) * I)‖ ≤ A / (1 + |t|) ^ 4)
    (hu : ‖spectralJRegularizerPrimitive L (((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4)‖ ≤ U) :
    ‖spectralJRegularizedBase f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ Real.pi * A * U / (1 + t ^ 2) ^ 2 := by
  have hpoly : (1 + t ^ 2) ^ 2 ≤ (1 + |t|) ^ 4 := by
    have h : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith only [sq_abs t, abs_nonneg t]
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + t ^ 2) h 2
  have hb' : (1 + t ^ 2) ^ 2 * ‖spectralJForwardTransform f ((t : ℂ) + (y : ℂ) * I)‖ ≤ A := by
    have h := (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 4)).mp hb
    exact (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)).trans (by simpa only [mul_comm] using h)
  apply (le_div_iff₀ (by positivity : 0 < (1 + t ^ 2) ^ 2)).mpr
  rw [spectralJRegularizedBase, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ = Real.pi * ((1 + t ^ 2) ^ 2 * ‖spectralJForwardTransform f ((t : ℂ) + (y : ℂ) * I)‖) *
        ‖spectralJRegularizerPrimitive L (((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4)‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hb' Real.pi_pos.le) hu (norm_nonneg _) (by positivity)

private theorem spectralJBase_argument_re (t y : ℝ) :
    ((((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4) : ℂ).re = t ^ 2 - y ^ 2 + 1 / 4 := by
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem spectralJRegularizedBase_fixed_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) (L : ℝ) (hL : 0 ≤ L) :
    ∃ B : ℝ, 0 < B ∧ ∀ t y : ℝ, 0 ≤ y → y ≤ 5 / 8 →
      ‖spectralJRegularizedBase f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ B / (1 + t ^ 2) ^ 2 := by
  obtain ⟨A, hA, ha⟩ := spectralJForwardTransform_strip_rapid f hf hc hp 4
  let U := L * Real.exp (L * (5 / 16))
  refine ⟨Real.pi * A * U + 1, by dsimp [U]; positivity, ?_⟩
  intro t y hy0 hy1
  have hb : ‖spectralJForwardTransform f ((t : ℂ) + (y : ℂ) * I)‖ ≤ A / (1 + |t|) ^ 4 := by
    simpa using ha ((t : ℂ) + (y : ℂ) * I) (by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero, zero_add]
      rw [abs_of_nonneg hy0]
      linarith)
  have hu : ‖spectralJRegularizerPrimitive L (((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4)‖ ≤ U := by
    apply spectralJRegularizerPrimitive_norm_le L (5 / 16) hL (by norm_num)
    rw [spectralJBase_argument_re]
    nlinarith only [sq_nonneg t, hy0, hy1]
  exact (spectralJRegularizedBase_bound f L A U t y hA (by dsimp [U]; positivity) hb hu).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

theorem spectralJRegularizedBase_inner_uniform_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ∃ B : ℝ, 0 < B ∧ ∀ L : ℝ, 0 ≤ L → ∀ t : ℝ,
      ‖spectralJRegularizedBase f L ((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I)‖ ≤ B / (1 + t ^ 2) ^ 2 := by
  obtain ⟨A, hA, ha⟩ := spectralJForwardTransform_strip_rapid f hf hc hp 4
  refine ⟨Real.pi * A * (128 / 7) + 1, by positivity, ?_⟩
  intro L hL t
  have hb : ‖spectralJForwardTransform f ((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I)‖ ≤ A / (1 + |t|) ^ 4 := by
    simpa using ha ((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I) (by norm_num)
  have hu : ‖spectralJRegularizerPrimitive L (((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I) ^ 2 + 1 / 4)‖ ≤
      128 / 7 := by
    have harg : (7 / 64 : ℝ) ≤ ((((t : ℂ) + ((3 / 8 : ℝ) : ℂ) * I) ^ 2 + 1 / 4) : ℂ).re := by
      rw [spectralJBase_argument_re]
      nlinarith only [sq_nonneg t]
    convert spectralJRegularizerPrimitive_norm_le_of_re_pos L (7 / 64) hL (by norm_num) _ harg using 1
    <;> norm_num
  exact (spectralJRegularizedBase_bound f L A (128 / 7) t (3 / 8) hA (by norm_num) hb hu).trans
    (div_le_div_of_nonneg_right (by linarith) (by positivity))

end
end ArtinMatthews
