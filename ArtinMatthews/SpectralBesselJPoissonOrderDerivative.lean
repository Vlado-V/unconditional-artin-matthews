module

public import ArtinMatthews.SpectralBesselJOrderDomination
public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselPoisson
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Monotonicity.Lemmas
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

/-! Differentiation in complex order under the actual Poisson integral,
with all measurability and beta-weight domination discharged. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralBesselJPoissonIntegral (X : ℝ) (ν : ℂ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, spectralBesselJPoissonIntegrand X ν u

def spectralBesselJPoissonDerivativeIntegral (X : ℝ) (ν : ℂ) : ℂ :=
  ∫ u in Ioo (-1 : ℝ) 1, spectralBesselJPoissonOrderDerivative X ν u

theorem spectralBesselJPoissonIntegrand_continuousOn (X : ℝ) (ν : ℂ) :
    ContinuousOn (spectralBesselJPoissonIntegrand X ν) (Ioo (-1 : ℝ) 1) := by
  have hc : ContinuousOn (fun u : ℝ => (spectralBesselJPoissonBase u : ℂ)) (Ioo (-1 : ℝ) 1) := by
    unfold spectralBesselJPoissonBase
    fun_prop
  have hp := hc.cpow (continuousOn_const (c := ν-1/2))
    (fun _ hu => Complex.ofReal_mem_slitPlane.mpr (spectralBesselJPoissonBase_pos hu))
  exact (by fun_prop : Continuous (fun u : ℝ => Complex.exp (Complex.I*(X : ℂ)*(u : ℂ)))).continuousOn.mul hp

theorem spectralBesselJPoissonOrderDerivative_continuousOn (X : ℝ) (ν : ℂ) :
    ContinuousOn (spectralBesselJPoissonOrderDerivative X ν) (Ioo (-1 : ℝ) 1) := by
  have hc : ContinuousOn (fun u : ℝ => (spectralBesselJPoissonBase u : ℂ)) (Ioo (-1 : ℝ) 1) := by
    unfold spectralBesselJPoissonBase
    fun_prop
  exact (spectralBesselJPoissonIntegrand_continuousOn X ν).mul
    (hc.clog (fun _ hu => Complex.ofReal_mem_slitPlane.mpr (spectralBesselJPoissonBase_pos hu)))

theorem spectralBesselJPoissonIntegrand_integrable (X : ℝ) {ν : ℂ} (hν : -(1/2 : ℝ) < ν.re) :
    IntegrableOn (spectralBesselJPoissonIntegrand X ν) (Ioo (-1 : ℝ) 1) := by
  have hi := spectralBesselJPoissonRealWeight_integrable (a := ν.re-1/2) (by linarith)
  apply hi.mono' ((spectralBesselJPoissonIntegrand_continuousOn X ν).aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have he : (ν-1/2).re = ν.re-1/2 := by norm_num
  simp only [spectralBesselJPoissonIntegrand,norm_mul,spectral_besselJ_poisson_phase_norm,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (spectralBesselJPoissonBase_pos hu),he,le_refl]

theorem spectralBesselJPoissonIntegrand_order_hasDerivAt (X : ℝ) (ν : ℂ) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun ζ : ℂ => spectralBesselJPoissonIntegrand X ζ u)
      (spectralBesselJPoissonOrderDerivative X ν u) ν := by
  have hbase : (spectralBesselJPoissonBase u : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (spectralBesselJPoissonBase_pos hu).ne'
  have hd := ((hasDerivAt_id ν).sub_const (1/2 : ℂ)).const_cpow
    (c := (spectralBesselJPoissonBase u : ℂ)) (Or.inl hbase)
  simpa only [spectralBesselJPoissonIntegrand,spectralBesselJPoissonOrderDerivative,id_eq,mul_one,mul_assoc]
    using hd.const_mul (Complex.exp (Complex.I*(X : ℂ)*(u : ℂ)))

theorem spectralBesselJPoissonIntegral_order_hasDerivAt (X : ℝ) {ν : ℂ}
    (hν : ν ∈ Metric.ball (0 : ℂ) (1/8)) :
    HasDerivAt (spectralBesselJPoissonIntegral X) (spectralBesselJPoissonDerivativeIntegral X ν) ν := by
  have hνn : ‖ν‖ < 1/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hν
  have hre : -(1/2 : ℝ) < ν.re := by linarith [(abs_le.mp (Complex.abs_re_le_norm ν)).1]
  have hb := (spectralBesselJPoissonRealWeight_integrable (a := -(7/8 : ℝ)) (by norm_num)).const_mul 4
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := spectralBesselJPoissonIntegrand X) (F' := spectralBesselJPoissonOrderDerivative X)
    (s := Metric.ball (0 : ℂ) (1/8)) (Metric.isOpen_ball.mem_nhds hν)
    (Filter.Eventually.of_forall (fun ζ =>
      (spectralBesselJPoissonIntegrand_continuousOn X ζ).aestronglyMeasurable measurableSet_Ioo))
    (spectralBesselJPoissonIntegrand_integrable X hre)
    ((spectralBesselJPoissonOrderDerivative_continuousOn X ν).aestronglyMeasurable measurableSet_Ioo)
    ?_ hb ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    intro ζ hζ
    exact spectralBesselJPoissonOrderDerivative_bound X hζ hu
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    intro ζ _
    exact spectralBesselJPoissonIntegrand_order_hasDerivAt X ζ hu

theorem spectral_besselJ_poisson_setIntegral (X : ℝ) {ν : ℂ} (hν : -(1/2 : ℝ) < ν.re) :
    Complex.besselJ ν (X : ℂ) =
      ((X : ℂ)/2)^ν/((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2))*spectralBesselJPoissonIntegral X ν := by
  rw [spectral_besselJ_poisson ν (X : ℂ) hν,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u _
  dsimp only [spectralBesselJPoissonIntegrand,spectralBesselJPoissonBase]
  push_cast
  rfl

end ArtinMatthews
