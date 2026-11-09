module

public import ArtinMatthews.SpectralWeylHeightCutoff
public import ArtinMatthews.SpectralLpTestMultiplier
public import ArtinMatthews.SpectralKLUnitary


set_option backward.privateInPublic true
@[expose] public section

/-! The literal exhausting height cutoffs converge strongly on the full
physical KL L2 space. Unitarity transports this actual convergence to
the spectral side. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace BoundedContinuousFunction
namespace ArtinMatthews

def spectralWeylCutoffSymbol (a : ℝ) (K : ℕ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (spectralHeightAnnularPartial K (a*x) : ℂ))
    (Complex.continuous_ofReal.comp ((spectralHeightAnnularPartial_continuous K).comp (by fun_prop)))
    1 (fun x => by
      rw [Complex.norm_real,Real.norm_of_nonneg (spectralHeightAnnularPartial_bounds _ _).1]
      exact (spectralHeightAnnularPartial_bounds _ _).2)

def spectralWeylCutoffLp (a : ℝ) (K : ℕ) (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    Lp ℂ 2 spectralKLPhysicalMeasure :=
  spectralLpTestMultiplier spectralKLPhysicalMeasure (spectralWeylCutoffSymbol a K) f

theorem spectralWeylCutoffLp_ae (a : ℝ) (K : ℕ) (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    spectralWeylCutoffLp a K f =ᵐ[spectralKLPhysicalMeasure] spectralWeylProfileCutoff a K f :=
  spectralLpTestMultiplier_ae _ _ _

theorem spectralWeylCutoffLp_tendsto {a : ℝ} (ha : 0 < a)
    (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    Tendsto (fun K : ℕ => spectralWeylCutoffLp a K f) atTop (𝓝 f) := by
  have hAll : ∀ᵐ x ∂spectralKLPhysicalMeasure,
      ∀ K : ℕ, spectralWeylCutoffLp a K f x = spectralWeylProfileCutoff a K f x :=
    ae_all_iff.mpr (fun K => spectralWeylCutoffLp_ae a K f)
  have hbound (K : ℕ) : ∀ᵐ x ∂spectralKLPhysicalMeasure,
      ‖spectralWeylCutoffLp a K f x-f x‖^2 ≤ 4*‖f x‖^2 := by
    filter_upwards [spectralWeylCutoffLp_ae a K f] with x hx
    rw [hx]
    have hnorm : ‖spectralWeylProfileCutoff a K f x-f x‖ ≤ 2*‖f x‖ := by
      calc
        _ ≤ ‖spectralWeylProfileCutoff a K f x‖+‖f x‖ := norm_sub_le _ _
        _ ≤ ‖f x‖+‖f x‖ := add_le_add (spectralWeylProfileCutoff_norm_le a K f x) le_rfl
        _ = _ := by ring
    have hs := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith
  have hlim : ∀ᵐ x ∂spectralKLPhysicalMeasure,
      Tendsto (fun K : ℕ => ‖spectralWeylCutoffLp a K f x-f x‖^2) atTop (𝓝 0) := by
    filter_upwards [hAll,spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx hp
    apply tendsto_const_nhds.congr'
    filter_upwards [spectralHeightAnnularPartial_eventually_one (mul_pos ha hp)] with K hK
    rw [hx K,spectralWeylProfileCutoff,hK,Complex.ofReal_one,one_mul,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  have hD : Integrable (fun x => 4*‖f x‖^2) spectralKLPhysicalMeasure :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).const_mul 4
  have hint : Tendsto (fun K : ℕ => ∫ x, ‖spectralWeylCutoffLp a K f x-f x‖^2 ∂spectralKLPhysicalMeasure)
      atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun x => 4*‖f x‖^2)
      (fun K => ((Lp.aestronglyMeasurable (spectralWeylCutoffLp a K f)).sub
        (Lp.aestronglyMeasurable f)).norm.pow 2) hD
      (fun K => (hbound K).mono (fun x hx => by
        change ‖‖spectralWeylCutoffLp a K f x-f x‖^2‖ ≤ 4*‖f x‖^2
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx)) hlim
    simpa only [Pi.pow_apply,Pi.sub_apply,integral_zero] using h
  have he (K : ℕ) : ‖spectralWeylCutoffLp a K f-f‖^2 =
      ∫ x, ‖spectralWeylCutoffLp a K f x-f x‖^2 ∂spectralKLPhysicalMeasure := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (spectralWeylCutoffLp a K f) f] with x hx
    rw [real_inner_self_eq_norm_sq,hx]
    rfl
  have hs : Tendsto (fun K : ℕ => ‖spectralWeylCutoffLp a K f-f‖^2) atTop (𝓝 0) := by
    simpa only [he] using hint
  have hn : Tendsto (fun K : ℕ => ‖spectralWeylCutoffLp a K f-f‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [Function.comp_def,Real.sqrt_zero,Real.sqrt_sq_eq_abs,abs_norm] using h
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hn

theorem spectralKLAnalysis_cutoff_tendsto {a : ℝ} (ha : 0 < a)
    (f : Lp ℂ 2 spectralKLPhysicalMeasure) :
    Tendsto (fun K : ℕ => spectralKLAnalysis (spectralWeylCutoffLp a K f)) atTop
      (𝓝 (spectralKLAnalysis f)) :=
  (spectralKLAnalysis.continuous.tendsto f).comp (spectralWeylCutoffLp_tendsto ha f)

end ArtinMatthews
