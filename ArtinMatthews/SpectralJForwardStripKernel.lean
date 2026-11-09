module

public import ArtinMatthews.SpectralBesselJSignedStrip
public import ArtinMatthews.SpectralJForwardTransform
public import Mathlib.Analysis.Real.Pi.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The exact divided kernel has polynomial growth on compact positive x
through the closed spectral strip |Im z| ≤ 3/4. -/
noncomputable section
open Set Complex

namespace ArtinMatthews

theorem spectralJForwardKernel_denominator_lower {z : ℂ} (hz : 1 ≤ |z.re|) :
    Real.exp (Real.pi*|z.re|)/2 ≤ ‖2*Complex.sin ((Real.pi : ℂ)*I*z)‖ := by
  let a := Real.pi*|z.re|
  let p := (Real.pi : ℂ)*z
  have he : 2*Complex.sin ((Real.pi : ℂ)*I*z) = (Complex.exp p-Complex.exp (-p))*I := by
    unfold Complex.sin
    have hp : ((Real.pi : ℂ)*I*z)*I = -p := by
      calc
        _ = p*I^2 := by dsimp [p]; ring
        _ = _ := by rw [I_sq]; ring
    rw [neg_mul, hp, neg_neg]
    ring
  have hN : ‖2*Complex.sin ((Real.pi : ℂ)*I*z)‖ = ‖Complex.exp p-Complex.exp (-p)‖ := by
    rw [he,norm_mul,Complex.norm_I,mul_one]
  have hp : p.re = Real.pi*z.re := by simp [p,Complex.mul_re]
  have hDiff := abs_norm_sub_norm_le (Complex.exp p) (Complex.exp (-p))
  rw [Complex.norm_exp,Complex.norm_exp,Complex.neg_re,hp,← hN] at hDiff
  have hAbs : |Real.exp (Real.pi*z.re)-Real.exp (-(Real.pi*z.re))| =
      Real.exp a-Real.exp (-a) := by
    rcases le_total 0 z.re with hp | hn
    · rw [show a = Real.pi*z.re by dsimp [a]; rw [abs_of_nonneg hp],
        abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by
          linarith only [mul_nonneg Real.pi_pos.le hp])))]
    · rw [show a = -(Real.pi*z.re) by dsimp [a]; rw [abs_of_nonpos hn]; ring,
        neg_neg, abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by
          linarith only [mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hn])))]
      ring
  rw [hAbs] at hDiff
  have hA : 1 ≤ a := by
    dsimp only [a]
    exact (show (1 : ℝ) ≤ Real.pi by linarith only [Real.pi_gt_three]).trans
      (le_mul_of_one_le_right Real.pi_pos.le hz)
  have hE : 2 ≤ Real.exp a := by linarith only [Real.add_one_le_exp a,hA]
  have hEm : Real.exp (-a) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  change Real.exp a/2 ≤ _
  linarith

theorem spectralJForwardKernel_strip_on_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.im| ≤ 3/4 → 1 ≤ |z.re| →
      ∀ x ∈ Icc a b, ‖spectralJForwardKernel z x‖ ≤ C*(1+|z.re|)^3 := by
  obtain ⟨C,hC,hB⟩ := spectral_besselJ_signed_strip_on_Icc (b := b) ha
  refine ⟨4*C, by positivity, ?_⟩
  intro z hIm hRe x hx
  let T := 1+|z.re|
  let E := Real.exp (Real.pi*|z.re|)
  have hD := spectralJForwardKernel_denominator_lower hRe
  have hD₀ : 0 < ‖2*Complex.sin ((Real.pi : ℂ)*I*z)‖ :=
    (half_pos (Real.exp_pos _)).trans_le hD
  have hz : z ≠ 0 := by
    intro he
    rw [he, Complex.zero_re, abs_zero] at hRe
    norm_num at hRe
  have hIm' : |2*z.im| ≤ 3/2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  have h₁ : ‖Complex.besselJ (-2*I*z) (x : ℂ)‖ ≤ C*T^3*E := by
    rw [show -2*I*z = ((2*z.im : ℝ) : ℂ)+2*((-z.re : ℝ) : ℂ)*I by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring]
    simpa only [T,E,abs_neg] using hB (2*z.im) (-z.re) x hIm' hx
  have h₂ : ‖Complex.besselJ (2*I*z) (x : ℂ)‖ ≤ C*T^3*E := by
    rw [show 2*I*z = ((-(2*z.im) : ℝ) : ℂ)+2*(z.re : ℂ)*I by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring]
    exact hB (-(2*z.im)) z.re x (by rwa [abs_neg]) hx
  rw [spectralJForwardKernel_of_ne_zero hz, norm_div]
  apply (div_le_iff₀ hD₀).mpr
  calc
    _ ≤ C*T^3*E+C*T^3*E := (norm_sub_le _ _).trans (add_le_add h₁ h₂)
    _ = (4*C*T^3)*(E/2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hD (by dsimp [T]; positivity)

end ArtinMatthews
