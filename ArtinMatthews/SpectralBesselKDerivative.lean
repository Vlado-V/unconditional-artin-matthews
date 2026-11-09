module

public import ArtinMatthews.SpectralBesselKConvergence
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! Actual differentiation of the arbitrary-order Schläfli integral.
The derivative majorant is another convergent Schläfli kernel at a fixed
positive lower bound for the argument. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralSchlafliKernel (ν : ℂ) (x t : ℝ) : ℂ :=
  (t : ℂ) ^ (ν - 1) * Complex.exp (-(t : ℂ) - (x : ℂ) ^ 2 / (4 * t))

theorem spectralSchlafliKernel_shift (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    spectralSchlafliKernel (ν - 1) x t = spectralSchlafliKernel ν x t / (t : ℂ) := by
  unfold spectralSchlafliKernel
  rw [Complex.cpow_sub (ν - 1) 1 (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
  ring

def spectralSchlafliKernelXDeriv (ν : ℂ) (x t : ℝ) : ℂ :=
  -((x : ℂ) / 2) * spectralSchlafliKernel (ν - 1) x t

theorem spectralSchlafliKernel_hasDerivAt (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ => spectralSchlafliKernel ν y t)
      (spectralSchlafliKernelXDeriv ν x t) x := by
  have he := (((((hasDerivAt_id x).ofReal_comp).pow 2).div_const
    (4 * (t : ℂ))).const_sub (-(t : ℂ))).cexp.const_mul ((t : ℂ) ^ (ν - 1))
  convert! he using 1
  unfold spectralSchlafliKernelXDeriv
  rw [spectralSchlafliKernel_shift ν x t ht]
  unfold spectralSchlafliKernel
  simp only [id_eq, Complex.ofReal_one, mul_one, Nat.cast_ofNat, Pi.pow_apply]
  field_simp
  ring

theorem spectralSchlafliKernelXDeriv_bound (ν : ℂ) (δ B x t : ℝ)
    (hδ : 0 < δ) (hx : δ ≤ x) (hB : x ≤ B) (ht : 0 < t) :
    ‖spectralSchlafliKernelXDeriv ν x t‖ ≤
      (B / 2) * (t ^ ((ν.re - 1) - 1) * Real.exp (-t - (δ ^ 2 / 4) / t)) := by
  have hxpos : 0 < x := hδ.trans_le hx
  have hBpos : 0 < B := hxpos.trans_le hB
  rw [spectralSchlafliKernelXDeriv, norm_mul, norm_neg, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
  norm_num
  rw [spectralSchlafliKernel, spectral_schlafli_kernel_norm (ν - 1) x t ht]
  simp only [Complex.sub_re, Complex.one_re]
  apply mul_le_mul
  · exact div_le_div_of_nonneg_right hB (by norm_num)
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
    apply Real.exp_le_exp.mpr
    have hsq : δ ^ 2 ≤ x ^ 2 := sq_le_sq₀ hδ.le hxpos.le |>.mpr hx
    exact sub_le_sub_left (div_le_div_of_nonneg_right
      (div_le_div_of_nonneg_right hsq (by norm_num)) ht.le) (-t)
  · positivity
  · positivity

theorem schlafliIntegral_hasDerivAt_all_orders (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => OAI.CubicEisenstein.schlafliIntegral ν y)
      (-((x : ℂ) / 2) * OAI.CubicEisenstein.schlafliIntegral (ν - 1) x) x := by
  let δ : ℝ := x / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδx : δ < x := by dsimp [δ]; linarith
  have hs : Ioo δ (x + 1) ∈ 𝓝 x := Ioo_mem_nhds hδx (by linarith)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ y ∈ Ioo δ (x + 1),
      ‖spectralSchlafliKernelXDeriv ν y t‖ ≤
        ((x + 1) / 2) * (t ^ ((ν.re - 1) - 1) * Real.exp (-t - (δ ^ 2 / 4) / t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    exact spectralSchlafliKernelXDeriv_bound ν δ (x + 1) y t hδ hy.1.le hy.2.le ht
  have hmajor := (spectral_schlafli_real_integrable (ν.re - 1) (δ ^ 2 / 4)
    (by positivity : 0 < δ ^ 2 / 4)).const_mul ((x + 1) / 2)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := spectralSchlafliKernel ν) (F' := spectralSchlafliKernelXDeriv ν)
    (bound := fun t => ((x + 1) / 2) *
      (t ^ ((ν.re - 1) - 1) * Real.exp (-t - (δ ^ 2 / 4) / t))) hs
    (Eventually.of_forall (fun y => by unfold spectralSchlafliKernel; fun_prop))
    (schlafliIntegral_integrable_all_orders ν x hx)
    (by unfold spectralSchlafliKernelXDeriv spectralSchlafliKernel; fun_prop)
    hbound hmajor (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact fun y _ => spectralSchlafliKernel_hasDerivAt ν y t ht)
  have hi : (∫ t in Ioi (0 : ℝ), spectralSchlafliKernelXDeriv ν x t) =
      -((x : ℂ) / 2) * OAI.CubicEisenstein.schlafliIntegral (ν - 1) x := by
    simp only [spectralSchlafliKernelXDeriv]
    rw [integral_const_mul]
    rfl
  have hd := h.2
  rw [hi] at hd
  exact hd

end ArtinMatthews
