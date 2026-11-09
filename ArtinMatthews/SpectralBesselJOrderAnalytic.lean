module

public import ArtinMatthews.SpectralBesselJPoissonOrderDerivative
public import ArtinMatthews.SpectralBesselIOrderAnalytic


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

private theorem poisson_order_domination (X : ℝ) (ν₀ : ℂ) (hν₀ : -(1/2 : ℝ) < ν₀.re)
    {ν : ℂ} (hν : ν ∈ Metric.ball ν₀ ((ν₀.re+1/2)/4))
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖spectralBesselJPoissonOrderDerivative X ν u‖ ≤
      ((ν₀.re+1/2)/4)⁻¹ * spectralBesselJPoissonBase u ^
        (ν₀.re-1/2-2*((ν₀.re+1/2)/4)) := by
  let ε := (ν₀.re+1/2)/4
  let v := spectralBesselJPoissonBase u
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hv : 0 < v := spectralBesselJPoissonBase_pos hu
  have hv1 : v ≤ 1 := spectralBesselJPoissonBase_le_one u
  have hd : ‖ν-ν₀‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hν
  have hre : ν₀.re-1/2-ε ≤ ν.re-1/2 := by
    have hr := Complex.abs_re_le_norm (ν-ν₀)
    simp only [Complex.sub_re] at hr
    linarith [(abs_le.mp hr).1]
  have hp := Real.rpow_le_rpow_of_exponent_ge hv hv1 hre
  have hνre : (ν-1/2).re = ν.re-1/2 := by norm_num
  unfold spectralBesselJPoissonOrderDerivative spectralBesselJPoissonIntegrand
  rw [norm_mul, norm_mul, spectral_besselJ_poisson_phase_norm, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hv, hνre, ← Complex.ofReal_log hv.le,
    Complex.norm_real, Real.norm_eq_abs]
  change v ^ (ν.re-1/2)*|Real.log v| ≤ ε⁻¹*v ^ (ν₀.re-1/2-2*ε)
  calc
    _ ≤ v ^ (ν₀.re-1/2-ε)*(v ^ (-ε)/ε) :=
      mul_le_mul hp (spectral_bessel_poisson_log_bound hv hv1 hε) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show v ^ (ν₀.re-1/2-ε)*(v ^ (-ε)/ε) =
        ε⁻¹*(v ^ (ν₀.re-1/2-ε)*v ^ (-ε)) by ring,
        ← Real.rpow_add hv]
      congr 2
      ring

theorem spectralBesselJPoissonIntegral_order_hasDerivAt_full (X : ℝ) {ν : ℂ}
    (hν : -(1/2 : ℝ) < ν.re) :
    HasDerivAt (spectralBesselJPoissonIntegral X) (spectralBesselJPoissonDerivativeIntegral X ν) ν := by
  let ε := (ν.re+1/2)/4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : -1 < ν.re-1/2-2*ε := by dsimp [ε]; linarith
  have hb := (spectralBesselJPoissonRealWeight_integrable hexp).const_mul ε⁻¹
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := spectralBesselJPoissonIntegrand X) (F' := spectralBesselJPoissonOrderDerivative X)
    (s := Metric.ball ν ε) (Metric.ball_mem_nhds ν hε)
    (Eventually.of_forall fun μ =>
      (spectralBesselJPoissonIntegrand_continuousOn X μ).aestronglyMeasurable measurableSet_Ioo)
    (spectralBesselJPoissonIntegrand_integrable X hν)
    ((spectralBesselJPoissonOrderDerivative_continuousOn X ν).aestronglyMeasurable measurableSet_Ioo)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      intro μ hμ
      exact poisson_order_domination X ν hν hμ hu)
    hb
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      intro μ _
      exact spectralBesselJPoissonIntegrand_order_hasDerivAt X μ hu)).2

theorem spectral_besselJ_order_differentiableAt {X : ℝ} (hX : 0 < X) {ν : ℂ}
    (hν : -(1/2 : ℝ) < ν.re) :
    DifferentiableAt ℂ (fun μ => Complex.besselJ μ (X : ℂ)) ν := by
  have hbase : (X/2 : ℂ) ≠ 0 := by exact_mod_cast (half_pos hX).ne'
  have hN := ((hasDerivAt_id ν).const_cpow (c := (X/2 : ℂ)) (Or.inl hbase)).differentiableAt
  have harg : 0 < (ν+1/2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hG := ((Complex.hasDerivAt_Gamma_of_re_pos harg).comp ν
    ((hasDerivAt_id ν).add_const (1/2 : ℂ))).differentiableAt
  have hden : (Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos harg)
  have hD := (hN.div (hG.const_mul (Real.sqrt Real.pi : ℂ)) hden).mul
    (spectralBesselJPoissonIntegral_order_hasDerivAt_full X hν).differentiableAt
  apply hD.congr_of_eventuallyEq
  have hnh : ∀ᶠ μ : ℂ in 𝓝 ν, -(1/2 : ℝ) < μ.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hν
  filter_upwards [hnh] with μ hμ
  exact spectral_besselJ_poisson_setIntegral X hμ

end
end ArtinMatthews
