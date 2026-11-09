module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! An integrable function and its integrable derivative admit a pointwise
bound on a positive ray from an integrable derivative majorant. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectral_ray_point_bound (a : ℝ) (f H : ℝ → ℝ)
    (hf : ∀ y, a ≤ y → HasDerivAt f (deriv f y) y)
    (hfi : IntegrableOn f (Ioi a)) (hdi : IntegrableOn (deriv f) (Ioi a))
    (hHi : IntegrableOn H (Ioi a))
    (hbound : ∀ y, a < y → |deriv f y| ≤ H y) (x : ℝ) (hx : a ≤ x) :
    |f x| ≤ ∫ y in Ioi a,H y := by
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun y hy => hf y hy.le) hdi hfi
  have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi hx
  have he := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun y hy => hf y (hx.trans hy)) (hdi.mono_set hsub) hlim
  have hHpos : 0 ≤ᵐ[volume.restrict (Ioi a)] H := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact (abs_nonneg _).trans (hbound y hy)
  calc
    |f x| = ‖∫ y in Ioi x,deriv f y‖ := by rw [he];simp only [zero_sub,Real.norm_eq_abs,abs_neg]
    _ ≤ ∫ y in Ioi x,‖deriv f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in Ioi x,H y := by
      apply setIntegral_mono_on (hdi.mono_set hsub).norm (hHi.mono_set hsub) measurableSet_Ioi
      intro y hy
      simpa only [Real.norm_eq_abs] using hbound y (hx.trans_lt hy)
    _ ≤ ∫ y in Ioi a,H y :=
      setIntegral_mono_set hHi hHpos (Eventually.of_forall (fun _ hy => hsub hy))

end ArtinMatthews
