module

public import ArtinMatthews.SpectralWeylGammaPair


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

theorem spectral_weyl_gamma_pair_shift_bound (B : ℝ) (hB : 1/4 < B) (hB' : B < 3/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖spectralABLCoshCancellation ((t : ℂ) - (B : ℂ)*Complex.I) /
        Complex.Gamma (1 + 2*(B : ℂ) + 2*(t : ℂ)*Complex.I)‖ ≤ C*(1+|t|) := by
  have hB0 : 0 ≤ B := by linarith
  let a : ℝ := 3/2-B
  let b : ℝ := 2*B-1/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  let R := Real.Gamma a / Real.Gamma (a+b)
  let P := ‖(Real.sqrt Real.pi : ℂ)/(Real.pi : ℂ)‖
  have hR : 0 < R := div_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos (add_pos ha hb))
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨(B+2)*(P+1)*(R+1), by positivity, ?_⟩
  intro t
  let v : ℂ := ((1/2+B : ℝ) : ℂ) + (t : ℂ)*Complex.I
  have hv : 0 < v.re := by simp only [v, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]; linarith
  have hz : -Complex.I*(v-1/2) = (t : ℂ)-(B : ℂ)*Complex.I := by
    dsimp only [v]
    push_cast
    linear_combination -(t : ℂ)*Complex.I_sq
  have hd : 2*v = 1+2*(B : ℂ)+2*(t : ℂ)*Complex.I := by
    dsimp only [v]
    push_cast
    ring
  have hnum : Complex.Gamma (2-v) = star (Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
    change _ = (starRingEnd ℂ) (Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I))
    rw [← Complex.Gamma_conj]
    congr 1
    dsimp only [v, a]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hden : (((a+b : ℝ) : ℂ)+(t : ℂ)*Complex.I) = v+1/2 := by
    dsimp only [a, b, v]
    push_cast
    ring
  have hratio : ‖Complex.Gamma (2-v)/Complex.Gamma (v+1/2)‖ ≤ R := by
    calc
      _ = ‖Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I) /
          Complex.Gamma (((a+b : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖ := by
        simp only [hnum, ← hden, norm_div, norm_star]
      _ ≤ R := spectralGamma_vertical_ratio_le a b t ha hb
  have hpow : ‖(2 : ℂ)^(1-2*v)‖ ≤ 1 := by
    rw [show ‖(2 : ℂ)^(1-2*v)‖ = (2 : ℝ)^(1-2*v).re by
      simpa only [Complex.ofReal_ofNat] using
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2) (1-2*v)]
    have hre : (1-2*v).re = -2*B := by
      dsimp only [v]
      norm_num [Complex.mul_re]
      ring
    rw [hre]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hvnorm : ‖v‖ ≤ (B+2)*(1+|t|) := by
    calc
      ‖v‖ ≤ ‖((1/2+B : ℝ) : ℂ)‖ + ‖(t : ℂ)*Complex.I‖ := norm_add_le _ _
      _ = 1/2+B+|t| := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
          abs_of_nonneg (by linarith : 0 ≤ 1/2+B)]
      _ ≤ (B+2)*(1+|t|) := by nlinarith [abs_nonneg t, mul_nonneg (show 0 ≤ B by linarith) (abs_nonneg t)]
  rw [← hd, ← hz, spectral_weyl_gamma_pair_identity v hv]
  simp only [norm_mul]
  change ‖v‖ * ‖(2 : ℂ)^(1-2*v)‖ * P *
    ‖Complex.Gamma (2-v)/Complex.Gamma (v+1/2)‖ ≤ _
  have hfirst : ‖v‖ * ‖(2 : ℂ)^(1-2*v)‖ ≤ (B+2)*(1+|t|) := by
    simpa only [mul_one] using mul_le_mul hvnorm hpow (norm_nonneg _) (by positivity)
  have hsecond : ‖v‖ * ‖(2 : ℂ)^(1-2*v)‖ * P ≤ (B+2)*(1+|t|)*(P+1) :=
    mul_le_mul hfirst (by linarith) hP (by positivity)
  calc
    _ ≤ (B+2)*(1+|t|)*(P+1)*(R+1) :=
      mul_le_mul hsecond (hratio.trans (by linarith)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
