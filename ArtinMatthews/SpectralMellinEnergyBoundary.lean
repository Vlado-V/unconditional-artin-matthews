module

public import ArtinMatthews.SpectralKLDistributionalOrthogonality
public import Mathlib.Analysis.SpecificLimits.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Removing a positive Mellin regularization from a nonnegative energy.
Fatou first proves integrability; dominated convergence then identifies the
unregularized integral. No energy integrability is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

theorem spectral_mellin_energy_boundary (H : ℝ → ℝ)
    (hn : ∀ x : ℝ, 0 < x → 0 ≤ H x)
    (hi : ∀ ε : ℝ, 0 < ε → IntegrableOn (fun x : ℝ => x^(ε-1)*H x) (Ioi 0))
    (N : ℝ)
    (hlim : Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), x^(ε-1)*H x)
      (𝓝[>] (0 : ℝ)) (𝓝 N)) :
    IntegrableOn (fun x : ℝ => x^(-1 : ℝ)*H x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), x^(-1 : ℝ)*H x) = N := by
  let e : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Filter.Eventually.of_forall hepos⟩
  have hpoint : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => x^(e n-1)*H x) atTop (𝓝 (x^(-1 : ℝ)*H x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hc : ContinuousAt (fun ε : ℝ => x^(ε-1)*H x) 0 :=
      (((Real.continuous_const_rpow hx.ne').comp (continuous_id.sub continuous_const)).mul
        continuous_const).continuousAt
    simpa only [Function.comp_def,zero_sub] using hc.tendsto.comp (he.mono_right nhdsWithin_le_nhds)
  have hli : Tendsto (fun n : ℕ =>
      ∫⁻ x in Ioi (0 : ℝ), ‖x^(e n-1)*H x‖ₑ) atTop (𝓝 (ENNReal.ofReal N)) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.comp he)
    convert hh using 1
    funext n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hi (e n) (hepos n))]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (hn x hx))]
  have hi0 : IntegrableOn (fun x : ℝ => x^(-1 : ℝ)*H x) (Ioi 0) :=
    integrable_of_tendsto hpoint (fun n => (hi (e n) (hepos n)).aestronglyMeasurable)
      (by rw [hli.liminf_eq]; exact ENNReal.ofReal_ne_top)
  have hi1 : IntegrableOn H (Ioi (0 : ℝ)) := by simpa using hi 1 zero_lt_one
  have hdct : Tendsto (fun ε : ℝ => ∫ x in Ioi (0 : ℝ), x^(ε-1)*H x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in Ioi (0 : ℝ), x^(-1 : ℝ)*H x)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => x^(-1 : ℝ)*H x+H x)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hi ε hε).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (hn x hx))]
      by_cases hx1 : x ≤ 1
      · have hp : x^(ε-1) ≤ x^(-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith [hε.1])
        exact (mul_le_mul_of_nonneg_right hp (hn x hx)).trans (le_add_of_nonneg_right (hn x hx))
      · have hp : x^(ε-1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx1)
          (sub_nonpos.mpr hε.2.le)
        exact (mul_le_of_le_one_left (hn x hx) hp).trans
          (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hx.le _) (hn x hx)))
    · exact hi0.add hi1
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hc : ContinuousAt (fun ε : ℝ => x^(ε-1)*H x) 0 :=
        (((Real.continuous_const_rpow hx.ne').comp (continuous_id.sub continuous_const)).mul
          continuous_const).continuousAt
      simpa only [zero_sub] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact ⟨hi0,(tendsto_nhds_unique hdct hlim)⟩

end ArtinMatthews
