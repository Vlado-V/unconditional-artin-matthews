module

public import ArtinMatthews.SpectralKSquarePhysicalBand


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform small-height lower bound for the actual real-order
Schläfli K kernel, directly from its proved hyperbolic integral. -/

noncomputable section
open Set MeasureTheory Filter
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralKCoshKernel_real_order (ν x u : ℝ) :
    spectralKCoshKernel (ν : ℂ) x u =
      ((Real.exp (-x*Real.cosh u)*Real.cosh (ν*u) : ℝ) : ℂ) := by
  simp only [spectralKCoshKernel,Complex.ofReal_mul,Complex.ofReal_exp,Complex.ofReal_cosh,neg_mul]

theorem spectralKRealOrder_integrable (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => Real.exp (-x*Real.cosh u)*Real.cosh (ν*u)) (Ioi 0) := by
  have h := (spectralKCoshKernel_integrable (ν : ℂ) hx).re
  apply h.congr
  filter_upwards with u
  rw [spectralKCoshKernel_real_order]
  rfl

theorem schlafliBesselK_real_order_integral (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    schlafliBesselK (ν : ℂ) x =
      ((∫ u in Ioi (0 : ℝ), Real.exp (-x*Real.cosh u)*Real.cosh (ν*u) : ℝ) : ℂ) := by
  rw [schlafliBesselK_cosh_integral _ hx]
  simp_rw [spectralKCoshKernel_real_order]
  rw [integral_complex_ofReal]

theorem schlafliBesselK_real_order_re_nonneg (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    0 ≤ (schlafliBesselK (ν : ℂ) x).re := by
  rw [schlafliBesselK_real_order_integral ν hx,Complex.ofReal_re]
  exact integral_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)

theorem schlafliBesselK_real_order_small_height_lower {ν x : ℝ} (hν : 0 ≤ ν)
    (hx : 0 < x) (hx₁ : x ≤ 1) :
    (Real.exp (-Real.exp 1)/2)*x^(-ν) ≤ (schlafliBesselK (ν : ℂ) x).re := by
  let a := -Real.log x
  let f (u : ℝ) := Real.exp (-x*Real.cosh u)*Real.cosh (ν*u)
  let B := (Real.exp (-Real.exp 1)/2)*x^(-ν)
  have ha : 0 ≤ a := neg_nonneg.mpr (Real.log_nonpos hx.le hx₁)
  have hS : Ioc a (a+1) ⊆ Ioi (0 : ℝ) := fun _ hu => ha.trans_lt hu.1
  have hI := spectralKRealOrder_integrable ν hx
  have hb (u : ℝ) (hu : u ∈ Ioc a (a+1)) : B ≤ f u := by
    have hcu : Real.cosh u ≤ Real.exp u := by
      rw [Real.cosh_eq]
      have hu₀ : 0 < u := hS hu
      have he := Real.exp_le_exp.mpr (show -u ≤ u by linarith only [hu₀])
      linarith only [he]
    have hxe : x*Real.cosh u ≤ Real.exp 1 := by
      calc
        _ ≤ x*Real.exp u := mul_le_mul_of_nonneg_left hcu hx.le
        _ ≤ x*Real.exp (a+1) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hu.2) hx.le
        _ = _ := by
          dsimp only [a]
          rw [Real.exp_add,Real.exp_neg,Real.exp_log hx,← mul_assoc,mul_inv_cancel₀ hx.ne',one_mul]
    have hExp : Real.exp (-Real.exp 1) ≤ Real.exp (-x*Real.cosh u) := by
      rw [Real.exp_le_exp]
      linarith only [hxe]
    have hpow : x^(-ν) = Real.exp (ν*a) := by
      rw [Real.rpow_def_of_pos hx]
      dsimp only [a]
      congr 1
      ring
    have hC : x^(-ν)/2 ≤ Real.cosh (ν*u) := by
      rw [hpow,Real.cosh_eq]
      have hE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.1.le hν)
      linarith only [hE,Real.exp_pos (-(ν*u))]
    change (Real.exp (-Real.exp 1)/2)*x^(-ν) ≤ _
    rw [show (Real.exp (-Real.exp 1)/2)*x^(-ν) = Real.exp (-Real.exp 1)*(x^(-ν)/2) by ring]
    exact mul_le_mul hExp hC (div_nonneg (Real.rpow_nonneg hx.le _) (by norm_num)) (Real.exp_pos _).le
  rw [schlafliBesselK_real_order_integral ν hx,Complex.ofReal_re]
  change B ≤ ∫ u in Ioi (0 : ℝ), f u
  calc
    _ = ∫ _u in Ioc a (a+1), B := by
      rw [← intervalIntegral.integral_of_le (show a ≤ a+1 by linarith),
        intervalIntegral.integral_const,add_sub_cancel_left,one_smul]
    _ ≤ ∫ u in Ioc a (a+1), f u :=
      setIntegral_mono_on (integrableOn_const isCompact_Icc.measure_ne_top
        |>.mono_set (Ioc_subset_Icc_self : Ioc a (a+1) ⊆ Icc a (a+1)))
        (hI.mono_set hS) measurableSet_Ioc hb
    _ ≤ _ := setIntegral_mono_set hI
      (Eventually.of_forall (fun _ => mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le))
      (Eventually.of_forall (fun _ hu => hS hu))

end ArtinMatthews
