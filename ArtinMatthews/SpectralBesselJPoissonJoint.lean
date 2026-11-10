module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.SpectralBesselJPoissonOrderDerivative
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


set_option backward.privateInPublic true
@[expose] public section

/-! Joint order and argument continuity of the actual J Poisson integral. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology

namespace ArtinMatthews

private theorem spectralBesselJPoissonIntegral_joint_continuousAt {ν : ℂ} (x : ℝ)
    (hν : -(1/2 : ℝ) < ν.re) :
    ContinuousAt (fun p : ℂ × ℝ => spectralBesselJPoissonIntegral p.2 p.1) (ν,x) := by
  let α := (ν.re-3/2)/2
  have hα : -1 < α := by dsimp [α]; linarith
  have hcut : α+1/2 < ν.re := by dsimp [α]; linarith
  have he : ∀ᶠ p : ℂ × ℝ in 𝓝 (ν,x), α+1/2 < p.1.re :=
    (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).mem_nhds hcut
  unfold spectralBesselJPoissonIntegral
  apply continuousAt_of_dominated (F := fun p : ℂ × ℝ => spectralBesselJPoissonIntegrand p.2 p.1)
    (bound := fun u => spectralBesselJPoissonBase u^α)
  · exact Eventually.of_forall (fun p : ℂ × ℝ =>
      (spectralBesselJPoissonIntegrand_continuousOn p.2 p.1).aestronglyMeasurable measurableSet_Ioo)
  · filter_upwards [he] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hb := spectralBesselJPoissonBase_pos hu
    rw [spectralBesselJPoissonIntegrand, norm_mul, spectral_besselJ_poisson_phase_norm, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hb]
    apply Real.rpow_le_rpow_of_exponent_ge hb (spectralBesselJPoissonBase_le_one u)
    rw [Complex.sub_re]
    norm_num
    linarith
  · exact spectralBesselJPoissonRealWeight_integrable hα
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hbase : (spectralBesselJPoissonBase u : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (spectralBesselJPoissonBase_pos hu).ne'
    apply Continuous.continuousAt
    simp only [spectralBesselJPoissonIntegrand, Complex.cpow_def_of_ne_zero hbase]
    fun_prop

theorem spectral_besselJ_joint_continuousAt_halfPlane {ν : ℂ} {x : ℝ}
    (hν : -(1/2 : ℝ) < ν.re) (hx : 0 < x) :
    ContinuousAt (fun p : ℂ × ℝ => Complex.besselJ p.1 (p.2 : ℂ)) (ν,x) := by
  have harg : 0 < (ν+1/2).re := by rw [Complex.add_re]; norm_num; linarith
  have hArg : ContinuousAt (fun p : ℂ × ℝ => p.1+1/2) (ν,x) :=
    (continuous_fst.add continuous_const).continuousAt
  have hGamma : ContinuousAt Complex.Gamma (ν+1/2) :=
    (Complex.hasDerivAt_Gamma_of_re_pos harg).continuousAt
  have hg : ContinuousAt (fun p : ℂ × ℝ => Complex.Gamma (p.1+1/2)) (ν,x) :=
    hGamma.comp_of_eq hArg rfl
  have hxSlit : (x : ℂ)/2 ∈ Complex.slitPlane := by
    rw [show (x : ℂ)/2 = ((x/2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_mem_slitPlane.mpr (half_pos hx)
  have hb : ContinuousAt (fun p : ℂ × ℝ => (p.2 : ℂ)/2) (ν,x) :=
    ((Complex.continuous_ofReal.comp continuous_snd).div_const (2 : ℂ)).continuousAt
  have ho : ContinuousAt (fun p : ℂ × ℝ => p.1) (ν,x) := continuous_fst.continuousAt
  have hp := hb.cpow ho hxSlit
  have hden : (Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1/2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne')
      (Complex.Gamma_ne_zero_of_re_pos harg)
  have h := (hp.div (continuousAt_const.mul hg) hden).mul
    (spectralBesselJPoissonIntegral_joint_continuousAt x hν)
  apply h.congr
  filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).mem_nhds hν]
    with p hp
  exact (spectral_besselJ_poisson_setIntegral p.2 hp).symm

end ArtinMatthews
