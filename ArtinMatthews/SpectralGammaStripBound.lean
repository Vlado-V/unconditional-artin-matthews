module

public import ArtinMatthews.SpectralGammaVertical
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform reciprocal-Gamma control on a closed right half-strip,
obtained from the literal beta integral and one Gamma recurrence. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem spectralBetaMass_add_one_le (c : ℝ) (hc : 0 ≤ c) :
    spectralBetaMass (c+1) ≤ spectralBetaMass 1 := by
  have hi := (Complex.betaIntegral_convergent (u := (1/2 : ℂ))
    (v := ((c+1 : ℝ) : ℂ)) (by norm_num) (by change 0 < c+1; linarith)).norm
  have hj := (Complex.betaIntegral_convergent (u := (1/2 : ℂ))
    (v := (1 : ℂ)) (by norm_num) (by norm_num)).norm
  unfold spectralBetaMass
  apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) hi hj
  intro x hx
  rw [norm_mul,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hp : 0 < 1-x := sub_pos.mpr hx.2
  have hcast : ((1-x : ℝ) : ℂ) = 1-(x : ℂ) := by push_cast;rfl
  rw [← hcast,Complex.norm_cpow_eq_rpow_re_of_pos hp,
    Complex.norm_cpow_eq_rpow_re_of_pos hp]
  norm_num
  exact Real.rpow_le_one hp.le (by linarith [hx.1]) hc

theorem spectral_inv_gamma_closed_strip_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ c t : ℝ, 0 ≤ c → c ≤ B →
      ‖(Complex.Gamma (((c+1/2 : ℝ) : ℂ)+(t : ℂ)*Complex.I))⁻¹‖ ≤
        C*(1+|t|)*Real.exp (Real.pi*|t|/2) := by
  have hGamma : ContinuousOn Real.Gamma (Ioi (0 : ℝ)) := by
    intro x hx
    change 0 < x at hx
    exact (Real.differentiableAt_Gamma (fun n => by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun c : ℝ => (Real.Gamma (c+1))⁻¹) (Icc 0 B) := by
    apply ContinuousOn.inv₀
    · exact hGamma.comp (continuous_id.add continuous_const).continuousOn
        (fun c hc => by change 0 < c+1;linarith [hc.1])
    · intro c hc
      exact (Real.Gamma_pos_of_pos (by linarith [hc.1] : 0 < c+1)).ne'
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR 0 ⟨le_rfl,hB⟩)
  let D := spectralBetaMass 1*(R+1)
  have hD : 0 ≤ D := mul_nonneg (spectralBetaMass_nonneg 1) (by linarith)
  refine ⟨(B+1)*(D+1),by positivity,?_⟩
  intro c t hc0 hcB
  let z : ℂ := (((c+1/2 : ℝ) : ℂ)+(t : ℂ)*Complex.I)
  have hzre : z.re = c+1/2 := by simp [z,Complex.mul_re]
  have hz : z ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    rw [hzre] at hh
    norm_num at hh
    linarith
  have hg : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hzre];linarith)
  have hinv : (Complex.Gamma z)⁻¹ = z*(Complex.Gamma (z+1))⁻¹ := by
    rw [Complex.Gamma_add_one z hz]
    field_simp
  have hreal : (Real.Gamma (c+1))⁻¹ ≤ R+1 := by
    have hh := hR c ⟨hc0,hcB⟩
    have hh' : |(Real.Gamma (c+1))⁻¹| ≤ R := by simpa only [Real.norm_eq_abs] using hh
    exact (le_abs_self _).trans (hh'.trans (by linarith))
  have hratio : spectralBetaMass (c+1)/‖Complex.Gamma ((c+1 : ℝ) : ℂ)‖ ≤ D := by
    have hgp := Real.Gamma_pos_of_pos (by linarith : 0 < c+1)
    rw [Complex.Gamma_ofReal,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hgp,div_eq_mul_inv]
    exact mul_le_mul (spectralBetaMass_add_one_le c hc0) hreal
      (inv_nonneg.mpr hgp.le) (spectralBetaMass_nonneg 1)
  have hshift : ‖(Complex.Gamma (z+1))⁻¹‖ ≤ D*Real.exp (Real.pi*|t|/2) := by
    have h := spectral_inv_gamma_shifted_half_line (c+1) (by linarith) (t/2)
    have he : (⟨1/2,2*(t/2)⟩ : ℂ)+((c+1 : ℝ) : ℂ) = z+1 := by
      apply Complex.ext <;> simp [z] <;> ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    have he' : Real.pi*(|t|/2) = Real.pi*|t|/2 := by ring
    rw [he'] at h
    exact h.trans (mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg _))
  have hzn : ‖z‖ ≤ (B+1)*(1+|t|) := by
    calc
      ‖z‖ ≤ ‖((c+1/2 : ℝ) : ℂ)‖+‖(t : ℂ)*Complex.I‖ := norm_add_le _ _
      _ = c+1/2+|t| := by
        simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one,
          abs_of_nonneg (by linarith : 0 ≤ c+1/2)]
      _ ≤ (B+1)*(1+|t|) := by nlinarith [abs_nonneg t,mul_nonneg hB (abs_nonneg t)]
  change ‖(Complex.Gamma z)⁻¹‖ ≤ _
  rw [hinv,norm_mul]
  calc
    _ ≤ ((B+1)*(1+|t|))*(D*Real.exp (Real.pi*|t|/2)) :=
      mul_le_mul hzn hshift (norm_nonneg _) (by positivity)
    _ ≤ ((B+1)*(1+|t|))*((D+1)*Real.exp (Real.pi*|t|/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)) (by positivity)
    _ = _ := by ring

end ArtinMatthews
