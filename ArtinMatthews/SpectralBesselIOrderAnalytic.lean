module

public import ArtinMatthews.SpectralBesselI
public import ArtinMatthews.SpectralBesselJOrderDomination
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter
open scoped Topology
noncomputable section

def spectralBesselIPoissonIntegrand (X : ℝ) (ν : ℂ) (u : ℝ) : ℂ :=
  Complex.exp ((-X * u : ℝ) : ℂ) * (spectralBesselJPoissonBase u : ℂ) ^ (ν - 1 / 2)

def spectralBesselIPoissonOrderDerivative (X : ℝ) (ν : ℂ) (u : ℝ) : ℂ :=
  spectralBesselIPoissonIntegrand X ν u * Complex.log (spectralBesselJPoissonBase u : ℂ)

def spectralBesselIPoissonIntegral (X : ℝ) (ν : ℂ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, spectralBesselIPoissonIntegrand X ν u

theorem spectralBesselIPoissonIntegrand_continuousOn (X : ℝ) (ν : ℂ) :
    ContinuousOn (spectralBesselIPoissonIntegrand X ν) (Ioo (-1 : ℝ) 1) := by
  have hc : ContinuousOn (fun u : ℝ => (spectralBesselJPoissonBase u : ℂ)) (Ioo (-1 : ℝ) 1) := by
    unfold spectralBesselJPoissonBase
    fun_prop
  exact (by fun_prop : Continuous (fun u : ℝ => Complex.exp ((-X * u : ℝ) : ℂ))).continuousOn.mul
    (hc.cpow (continuousOn_const (c := ν - 1 / 2))
      (fun _ hu => Complex.ofReal_mem_slitPlane.mpr (spectralBesselJPoissonBase_pos hu)))

theorem spectralBesselIPoissonOrderDerivative_continuousOn (X : ℝ) (ν : ℂ) :
    ContinuousOn (spectralBesselIPoissonOrderDerivative X ν) (Ioo (-1 : ℝ) 1) := by
  have hc : ContinuousOn (fun u : ℝ => (spectralBesselJPoissonBase u : ℂ)) (Ioo (-1 : ℝ) 1) := by
    unfold spectralBesselJPoissonBase
    fun_prop
  exact (spectralBesselIPoissonIntegrand_continuousOn X ν).mul
    (hc.clog (fun _ hu => Complex.ofReal_mem_slitPlane.mpr (spectralBesselJPoissonBase_pos hu)))

theorem spectralBesselIPoissonIntegrand_norm (X : ℝ) (ν : ℂ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖spectralBesselIPoissonIntegrand X ν u‖ =
      Real.exp (-X * u) * spectralBesselJPoissonBase u ^ (ν.re - 1 / 2) := by
  unfold spectralBesselIPoissonIntegrand
  rw [norm_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.norm_cpow_eq_rpow_re_of_pos (spectralBesselJPoissonBase_pos hu)]
  norm_num

theorem spectralBesselIPoissonIntegrand_integrable {X : ℝ} (hX : 0 < X) {ν : ℂ}
    (hν : -(1 / 2 : ℝ) < ν.re) :
    IntegrableOn (spectralBesselIPoissonIntegrand X ν) (Ioo (-1 : ℝ) 1) := by
  have hi := (spectralBesselJPoissonRealWeight_integrable (a := ν.re - 1 / 2) (by linarith)).const_mul
    (Real.exp X)
  apply hi.mono' ((spectralBesselIPoissonIntegrand_continuousOn X ν).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [spectralBesselIPoissonIntegrand_norm X ν hu]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith [hu.1]))
    (Real.rpow_nonneg (spectralBesselJPoissonBase_pos hu).le _)

theorem spectral_bessel_poisson_log_bound {v ε : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hε : 0 < ε) :
    |Real.log v| ≤ v ^ (-ε) / ε := by
  rw [abs_of_nonpos (Real.log_nonpos hv.le hv1)]
  simpa only [neg_div, neg_neg] using neg_le_neg (Real.neg_rpow_div_le_log hv.le hε)

theorem spectralBesselIPoissonOrderDerivative_bound {X : ℝ} (hX : 0 < X) (ν₀ : ℂ)
    (hν₀ : -(1 / 2 : ℝ) < ν₀.re) {ν : ℂ}
    (hν : ν ∈ Metric.ball ν₀ ((ν₀.re + 1 / 2) / 4))
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖spectralBesselIPoissonOrderDerivative X ν u‖ ≤
      (Real.exp X / ((ν₀.re + 1 / 2) / 4)) *
        spectralBesselJPoissonBase u ^ (ν₀.re - 1 / 2 - 2 * ((ν₀.re + 1 / 2) / 4)) := by
  let ε := (ν₀.re + 1 / 2) / 4
  let v := spectralBesselJPoissonBase u
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hv : 0 < v := spectralBesselJPoissonBase_pos hu
  have hv1 : v ≤ 1 := spectralBesselJPoissonBase_le_one u
  have hd : ‖ν - ν₀‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hν
  have hre : ν₀.re - 1 / 2 - ε ≤ ν.re - 1 / 2 := by
    have hr := Complex.abs_re_le_norm (ν - ν₀)
    simp only [Complex.sub_re] at hr
    linarith [(abs_le.mp hr).1]
  have hp := Real.rpow_le_rpow_of_exponent_ge hv hv1 hre
  unfold spectralBesselIPoissonOrderDerivative
  rw [norm_mul, spectralBesselIPoissonIntegrand_norm X ν hu,
    ← Complex.ofReal_log hv.le, Complex.norm_real, Real.norm_eq_abs]
  change Real.exp (-X * u) * v ^ (ν.re - 1 / 2) * |Real.log v| ≤
    (Real.exp X / ε) * v ^ (ν₀.re - 1 / 2 - 2 * ε)
  calc
    _ ≤ Real.exp X * v ^ (ν₀.re - 1 / 2 - ε) * (v ^ (-ε) / ε) :=
      mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [hu.1])) hp
        (Real.rpow_nonneg hv.le _) (Real.exp_nonneg _))
        (spectral_bessel_poisson_log_bound hv hv1 hε) (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [show Real.exp X * v ^ (ν₀.re - 1 / 2 - ε) * (v ^ (-ε) / ε) =
        (Real.exp X / ε) * (v ^ (ν₀.re - 1 / 2 - ε) * v ^ (-ε)) by ring,
        ← Real.rpow_add hv]
      congr 2
      ring

theorem spectralBesselIPoissonIntegrand_order_hasDerivAt (X : ℝ) (ν : ℂ)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun μ => spectralBesselIPoissonIntegrand X μ u)
      (spectralBesselIPoissonOrderDerivative X ν u) ν := by
  have hbase : (spectralBesselJPoissonBase u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (spectralBesselJPoissonBase_pos hu).ne'
  have hd := ((hasDerivAt_id ν).sub_const (1 / 2 : ℂ)).const_cpow
    (c := (spectralBesselJPoissonBase u : ℂ)) (Or.inl hbase)
  simpa only [spectralBesselIPoissonIntegrand, spectralBesselIPoissonOrderDerivative,
    id_eq, mul_one, mul_assoc] using hd.const_mul (Complex.exp ((-X * u : ℝ) : ℂ))

theorem spectralBesselIPoissonIntegral_order_hasDerivAt {X : ℝ} (hX : 0 < X) {ν : ℂ}
    (hν : -(1 / 2 : ℝ) < ν.re) :
    HasDerivAt (spectralBesselIPoissonIntegral X)
      (∫ u in Ioo (-1 : ℝ) 1, spectralBesselIPoissonOrderDerivative X ν u) ν := by
  let ε := (ν.re + 1 / 2) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hexp : -1 < ν.re - 1 / 2 - 2 * ε := by dsimp [ε]; linarith
  have hb := (spectralBesselJPoissonRealWeight_integrable hexp).const_mul (Real.exp X / ε)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := spectralBesselIPoissonIntegrand X) (F' := spectralBesselIPoissonOrderDerivative X)
    (s := Metric.ball ν ε) (Metric.ball_mem_nhds ν hε)
    (Eventually.of_forall fun μ =>
      (spectralBesselIPoissonIntegrand_continuousOn X μ).aestronglyMeasurable measurableSet_Ioo)
    (spectralBesselIPoissonIntegrand_integrable hX hν)
    ((spectralBesselIPoissonOrderDerivative_continuousOn X ν).aestronglyMeasurable measurableSet_Ioo)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      intro μ hμ
      exact spectralBesselIPoissonOrderDerivative_bound hX ν hν hμ hu)
    hb
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      intro μ _
      exact spectralBesselIPoissonIntegrand_order_hasDerivAt X μ hu)).2

theorem spectralBesselI_order_differentiableAt {X : ℝ} (hX : 0 < X) {ν : ℂ}
    (hν : -(1 / 2 : ℝ) < ν.re) :
    DifferentiableAt ℂ (fun μ => spectralBesselI μ X) ν := by
  have hbase : (X / 2 : ℂ) ≠ 0 := by exact_mod_cast (half_pos hX).ne'
  have hN := ((hasDerivAt_id ν).const_cpow (c := (X / 2 : ℂ)) (Or.inl hbase)).differentiableAt
  have harg : 0 < (ν + 1 / 2).re := by simp only [Complex.add_re]; norm_num; linarith
  have hG := ((Complex.hasDerivAt_Gamma_of_re_pos harg).comp ν
    ((hasDerivAt_id ν).add_const (1 / 2 : ℂ))).differentiableAt
  have hden : (Real.sqrt Real.pi : ℂ) * Complex.Gamma (ν + 1 / 2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos harg)
  have hD := (hN.div (hG.const_mul (Real.sqrt Real.pi : ℂ)) hden).mul
    (spectralBesselIPoissonIntegral_order_hasDerivAt hX hν).differentiableAt
  apply hD.congr_of_eventuallyEq
  have hnh : ∀ᶠ μ : ℂ in 𝓝 ν, -(1 / 2 : ℝ) < μ.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hν
  filter_upwards [hnh] with μ hμ
  rw [spectralBesselI_poisson μ hX hμ,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  simp only [spectralBesselIPoissonIntegrand, spectralBesselJPoissonBase]
  push_cast
  rfl

end
end ArtinMatthews
