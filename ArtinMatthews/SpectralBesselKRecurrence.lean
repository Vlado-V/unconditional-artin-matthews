module

public import ArtinMatthews.SpectralBesselKDerivative
public import ArtinMatthews.SpectralBesselKConvergence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! Vanishing boundary terms and the actual Schläfli recurrence. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectralSchlafliKernel_tendsto_zero (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => spectralSchlafliKernel ν x t) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨n, hn⟩ := exists_nat_gt (1 - ν.re)
  have hs : 0 < (ν.re + (n : ℝ)) - 1 := by linarith
  have hc : 0 < x ^ 2 / 4 := by positivity
  have hp : Tendsto (fun t : ℝ => t ^ ((ν.re + n) - 1)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 ((ν.re + n) - 1)
      (Or.inr hs.le)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Real.zero_rpow hs.ne'] using h
  have he : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, neg_zero, Real.exp_zero] using
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hlim := (he.mul hp).const_mul ((n.factorial : ℝ) / (x ^ 2 / 4) ^ n)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [spectralSchlafliKernel, spectral_schlafli_kernel_norm ν x t ht]
  exact spectral_schlafli_real_majorant ν.re (x ^ 2 / 4) t hc ht n

theorem spectralSchlafliKernel_tendsto_atTop (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t : ℝ => spectralSchlafliKernel ν x t) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hc : 0 < x ^ 2 / 4 := by positivity
  have hlim := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (ν.re - 1) 1 zero_lt_one
  simp only [neg_mul, one_mul] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [spectralSchlafliKernel, spectral_schlafli_kernel_norm ν x t ht]
  simpa only [Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul,
    Nat.cast_zero, add_zero, mul_comm] using
    spectral_schlafli_real_majorant ν.re (x ^ 2 / 4) t hc ht 0

theorem spectralSchlafliKernel_t_hasDerivAt (ν : ℂ) (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => spectralSchlafliKernel (ν + 1) x u)
      (ν * spectralSchlafliKernel ν x t - spectralSchlafliKernel (ν + 1) x t +
        (x : ℂ) ^ 2 / 4 * spectralSchlafliKernel (ν - 1) x t) t := by
  have hp := ((hasDerivAt_id (t : ℂ)).cpow_const (c := ν)
    (Complex.ofReal_mem_slitPlane.mpr ht)).comp_ofReal
  have he := (((hasDerivAt_id t).ofReal_comp.neg).sub
    ((hasDerivAt_const t ((x : ℂ) ^ 2)).div
      ((hasDerivAt_id t).ofReal_comp.const_mul 4)
      (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr ht.ne')))).cexp
  have hd := hp.mul he
  dsimp only [id, Pi.mul_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at hd
  convert hd using 1
  · ext u
    simp only [spectralSchlafliKernel, add_sub_cancel_right]
    rfl
  · rw [spectralSchlafliKernel_shift ν x t ht]
    simp only [spectralSchlafliKernel, add_sub_cancel_right, Complex.ofReal_one,
      mul_one, zero_mul]
    rw [Complex.cpow_sub ν 1 (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
    field_simp
    ring

theorem schlafliIntegral_recurrence (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    OAI.CubicEisenstein.schlafliIntegral (ν + 1) x =
      ν * OAI.CubicEisenstein.schlafliIntegral ν x +
        (x : ℂ) ^ 2 / 4 * OAI.CubicEisenstein.schlafliIntegral (ν - 1) x := by
  let f := fun t : ℝ => spectralSchlafliKernel (ν + 1) x t
  let f' := fun t : ℝ => ν * spectralSchlafliKernel ν x t -
    spectralSchlafliKernel (ν + 1) x t +
    (x : ℂ) ^ 2 / 4 * spectralSchlafliKernel (ν - 1) x t
  have hi : IntegrableOn f' (Ioi 0) :=
    (((schlafliIntegral_integrable_all_orders ν x hx).const_mul ν).sub
      (schlafliIntegral_integrable_all_orders (ν + 1) x hx)).add
      ((schlafliIntegral_integrable_all_orders (ν - 1) x hx).const_mul ((x : ℂ) ^ 2 / 4))
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    exact spectralSchlafliKernel_t_hasDerivAt ν x t ht
  have h0 := spectralSchlafliKernel_tendsto_zero (ν + 1) x hx
  have htop := spectralSchlafliKernel_tendsto_atTop (ν + 1) x hx
  let g := Function.update f 0 0
  have hgderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (f' t) t := by
    intro t ht
    apply (hderiv t ht).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht.ne'] with u hu
    exact Function.update_of_ne hu 0 f
  have hgcont : ContinuousWithinAt g (Ici 0) 0 := by
    apply continuousWithinAt_update_same.mpr
    simpa only [Ici_sdiff_left] using h0
  have hgtop : Tendsto g atTop (𝓝 0) := by
    apply htop.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
    exact (Function.update_of_ne ht 0 f).symm
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto hgcont hgderiv hi hgtop
  simp only [g, Function.update_self, sub_self] at hz
  change (∫ t in Ioi (0 : ℝ), ν * spectralSchlafliKernel ν x t -
    spectralSchlafliKernel (ν + 1) x t +
    (x : ℂ) ^ 2 / 4 * spectralSchlafliKernel (ν - 1) x t) = 0 at hz
  have hleft : IntegrableOn (fun t => ν * spectralSchlafliKernel ν x t) (Ioi 0) :=
    (schlafliIntegral_integrable_all_orders ν x hx).const_mul ν
  have hright : IntegrableOn (fun t => (x : ℂ) ^ 2 / 4 *
      spectralSchlafliKernel (ν - 1) x t) (Ioi 0) :=
    (schlafliIntegral_integrable_all_orders (ν - 1) x hx).const_mul ((x : ℂ) ^ 2 / 4)
  have hmid : IntegrableOn (spectralSchlafliKernel (ν + 1) x) (Ioi 0) :=
    schlafliIntegral_integrable_all_orders (ν + 1) x hx
  have hsub : IntegrableOn (fun t => ν * spectralSchlafliKernel ν x t -
      spectralSchlafliKernel (ν + 1) x t) (Ioi 0) := hleft.sub hmid
  rw [integral_add hsub hright, integral_sub hleft hmid, integral_const_mul,
    integral_const_mul] at hz
  change ν * OAI.CubicEisenstein.schlafliIntegral ν x -
    OAI.CubicEisenstein.schlafliIntegral (ν + 1) x +
    (x : ℂ) ^ 2 / 4 * OAI.CubicEisenstein.schlafliIntegral (ν - 1) x = 0 at hz
  linear_combination -hz

end ArtinMatthews
