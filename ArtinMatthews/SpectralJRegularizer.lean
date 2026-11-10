module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Filter Set MeasureTheory
open scoped Topology
noncomputable section

/-- The entire extension of `(1 - exp (-L*w)) / w`, with value `L` at zero. -/
def spectralJRegularizerPrimitive (L : ℝ) (w : ℂ) : ℂ :=
  -dslope (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) 0 w

theorem spectralJRegularizerPrimitive_zero (L : ℝ) :
    spectralJRegularizerPrimitive L 0 = (L : ℂ) := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) (-(L : ℂ)) 0 := by
    simpa only [id_eq, mul_zero, Complex.exp_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℂ)).const_mul (-(L : ℂ))).cexp
  simp only [spectralJRegularizerPrimitive, dslope_same, h.deriv, neg_neg]

theorem spectralJRegularizerPrimitive_differentiable (L : ℝ) :
    Differentiable ℂ (spectralJRegularizerPrimitive L) := by
  have h : Differentiable ℂ (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) := by fun_prop
  have hd : DifferentiableOn ℂ (dslope (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) 0) univ :=
    (Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr h.differentiableOn
  exact (differentiableOn_univ.mp hd).neg

theorem spectralJRegularizerPrimitive_mul (L : ℝ) (w : ℂ) :
    w * spectralJRegularizerPrimitive L w = 1 - Complex.exp (-(L : ℂ) * w) := by
  have h := sub_smul_dslope (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) 0 w
  simp only [sub_zero, smul_eq_mul, mul_zero, Complex.exp_zero] at h
  dsimp only [spectralJRegularizerPrimitive]
  calc
    _ = -(w * dslope (fun z : ℂ => Complex.exp (-(L : ℂ) * z)) 0 w) := by ring
    _ = _ := by rw [h]; ring

theorem spectralJRegularizerPrimitive_of_ne_zero (L : ℝ) {w : ℂ} (hw : w ≠ 0) :
    spectralJRegularizerPrimitive L w = (1 - Complex.exp (-(L : ℂ) * w)) / w := by
  apply (eq_div_iff hw).mpr
  simpa only [mul_comm] using spectralJRegularizerPrimitive_mul L w

theorem spectralJRegularizerPrimitive_integral (L : ℝ) (w : ℂ) :
    spectralJRegularizerPrimitive L w =
      ∫ s in (0 : ℝ)..L, Complex.exp (-(s : ℂ) * w) := by
  by_cases hw : w = 0
  · subst w
    simp only [spectralJRegularizerPrimitive_zero, mul_zero, Complex.exp_zero,
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, Complex.real_smul, mul_one]
  · rw [spectralJRegularizerPrimitive_of_ne_zero L hw]
    have he := integral_exp_mul_complex (a := (0 : ℝ)) (b := L) (c := -w) (neg_ne_zero.mpr hw)
    have hfun : (fun s : ℝ => Complex.exp (-(s : ℂ) * w)) =
        (fun s : ℝ => Complex.exp (-w * (s : ℂ))) := by
      funext s
      congr 1
      ring
    rw [hfun, he]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_mul]
    field_simp [hw]
    <;> ring

theorem spectralJRegularizerPrimitive_norm_le (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (w : ℂ) (hw : -D ≤ w.re) :
    ‖spectralJRegularizerPrimitive L w‖ ≤ L * Real.exp (L * D) := by
  rw [spectralJRegularizerPrimitive_integral]
  calc
    _ ≤ Real.exp (L * D) * |L - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [uIoc_of_le hL] at hs
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
        neg_zero, zero_mul, sub_zero]
      calc
        (-s) * w.re ≤ s * D := by nlinarith only [hw, hs.1.le]
        _ ≤ L * D := mul_le_mul_of_nonneg_right hs.2 hD
    _ = _ := by rw [sub_zero, abs_of_nonneg hL]; ring

theorem spectralJRegularizerPrimitive_norm_le_of_re_pos (L δ : ℝ) (hL : 0 ≤ L)
    (hδ : 0 < δ) (w : ℂ) (hw : δ ≤ w.re) :
    ‖spectralJRegularizerPrimitive L w‖ ≤ 2 / δ := by
  have hw0 : w ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hw; linarith
  have hexp : ‖Complex.exp (-(L : ℂ) * w)‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, zero_mul, sub_zero]
    nlinarith only [mul_nonneg hL (hδ.le.trans hw)]
  have hnorm : δ ≤ ‖w‖ := hw.trans (Complex.re_le_norm w)
  rw [spectralJRegularizerPrimitive_of_ne_zero L hw0, norm_div]
  have hnum : ‖(1 : ℂ) - Complex.exp (-(L : ℂ) * w)‖ ≤ 2 := by
    calc
      _ ≤ 1 + ‖Complex.exp (-(L : ℂ) * w)‖ := by simpa only [norm_one] using norm_sub_le (1 : ℂ) _
      _ ≤ 2 := by linarith only [hexp]
  exact (div_le_div_of_nonneg_right hnum
    (norm_nonneg w)).trans (div_le_div_of_nonneg_left (by norm_num) hδ hnorm)

end
end ArtinMatthews
