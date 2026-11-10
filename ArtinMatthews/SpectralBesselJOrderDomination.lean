module

public import ArtinMatthews.SpectralBesselPoissonMoments
public import ArtinMatthews.SpectralBesselPoissonSymmetry
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine order differentiation at zero starts from the proved J Poisson
integral.  A beta weight controls the logarithmic derivative uniformly
on a complex neighborhood of zero order. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralBesselJPoissonBase (u : ℝ) : ℝ := 1-u^2

def spectralBesselJPoissonIntegrand (X : ℝ) (ν : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I*(X : ℂ)*(u : ℂ))*(spectralBesselJPoissonBase u : ℂ)^(ν-1/2)

def spectralBesselJPoissonOrderDerivative (X : ℝ) (ν : ℂ) (u : ℝ) : ℂ :=
  spectralBesselJPoissonIntegrand X ν u*Complex.log (spectralBesselJPoissonBase u : ℂ)

theorem spectralBesselJPoissonBase_pos {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < spectralBesselJPoissonBase u := by
  unfold spectralBesselJPoissonBase
  nlinarith [mul_pos (sub_pos.mpr hu.2) (show 0 < 1+u by linarith [hu.1])]

theorem spectralBesselJPoissonBase_le_one (u : ℝ) : spectralBesselJPoissonBase u ≤ 1 := by
  unfold spectralBesselJPoissonBase
  exact sub_le_self _ (sq_nonneg u)

theorem spectralBesselJPoissonRealWeight_integrable {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun u : ℝ => spectralBesselJPoissonBase u^a) (Ioo (-1 : ℝ) 1) := by
  let ν : ℂ := ((a+1/2 : ℝ) : ℂ)
  have hν : -(1/2 : ℝ) < ν.re := by
    change -(1/2 : ℝ) < a+1/2
    linarith
  have hi0 : IntegrableOn (fun u : ℝ => ‖spectralPoissonMoment ν 0 u‖) (Ioc (-1 : ℝ) 1) :=
    (spectralPoissonMoment_integrable ν hν 0).1.norm
  have hi := hi0.mono_set (Ioo_subset_Ioc_self : Ioo (-1 : ℝ) 1 ⊆ Ioc (-1 : ℝ) 1)
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hc : 1-(u : ℂ)^2 = (spectralBesselJPoissonBase u : ℂ) := by
    unfold spectralBesselJPoissonBase
    push_cast
    rfl
  have he : (ν-1/2).re = a := by dsimp [ν]; norm_num
  rw [spectralPoissonMoment,pow_zero,one_mul,hc,
    Complex.norm_cpow_eq_rpow_re_of_pos (spectralBesselJPoissonBase_pos hu),he]

theorem spectral_besselJ_poisson_phase_norm (X u : ℝ) :
    ‖Complex.exp (Complex.I*(X : ℂ)*(u : ℂ))‖ = 1 := by
  have he : (Complex.I*(X : ℂ)*(u : ℂ)).re = 0 := by norm_num [Complex.mul_re,Complex.mul_im]
  rw [Complex.norm_exp,he,Real.exp_zero]

theorem spectral_besselJ_poisson_log_bound {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) :
    |Real.log v| ≤ 4*v^(-(1/4 : ℝ)) := by
  rw [abs_of_nonpos (Real.log_nonpos hv.le hv1)]
  have h := Real.neg_rpow_div_le_log hv.le (by norm_num : (0 : ℝ) < 1/4)
  linarith

theorem spectralBesselJPoissonOrderDerivative_bound (X : ℝ) {ν : ℂ}
    (hν : ν ∈ Metric.ball (0 : ℂ) (1/8)) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖spectralBesselJPoissonOrderDerivative X ν u‖ ≤ 4*spectralBesselJPoissonBase u^(-(7/8 : ℝ)) := by
  let v := spectralBesselJPoissonBase u
  have hv : 0 < v := spectralBesselJPoissonBase_pos hu
  have hv1 : v ≤ 1 := spectralBesselJPoissonBase_le_one u
  have hνn : ‖ν‖ < 1/8 := by simpa only [Metric.mem_ball,dist_zero_right] using hν
  have hνre : -(1/8 : ℝ) ≤ ν.re := by
    linarith [(abs_le.mp (Complex.abs_re_le_norm ν)).1]
  have hp : v^(ν.re-1/2) ≤ v^(-(5/8 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith)
  have he : (ν-1/2).re = ν.re-1/2 := by norm_num
  unfold spectralBesselJPoissonOrderDerivative spectralBesselJPoissonIntegrand
  change ‖Complex.exp (Complex.I*(X : ℂ)*(u : ℂ))*(v : ℂ)^(ν-1/2)*Complex.log (v : ℂ)‖ ≤
    4*v^(-(7/8 : ℝ))
  rw [norm_mul,norm_mul,spectral_besselJ_poisson_phase_norm,one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hv,he,← Complex.ofReal_log hv.le,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ v^(-(5/8 : ℝ))*(4*v^(-(1/4 : ℝ))) :=
      mul_le_mul hp (spectral_besselJ_poisson_log_bound hv hv1) (abs_nonneg _) (Real.rpow_nonneg hv.le _)
    _ = 4*v^(-(7/8 : ℝ)) := by
      rw [show v^(-(5/8 : ℝ))*(4*v^(-(1/4 : ℝ))) =
        4*(v^(-(5/8 : ℝ))*v^(-(1/4 : ℝ))) by ring,
        ← Real.rpow_add hv]
      norm_num

end ArtinMatthews
