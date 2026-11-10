module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralAntiKMellinEvaluation
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralMellinReciprocalScale
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit proposed Weber K value, with its independently proved
Mellin convergence and transport.  Equality to the Gaussian integral is
proved separately by Mellin uniqueness. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralWeberKClosed (ν : ℂ) (p : ℝ) : ℂ :=
  ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
    ((p : ℂ)^(-(1/2 : ℂ))*(Complex.exp (((1/8 : ℝ)/p : ℝ) : ℂ)*
      schlafliBesselK ν ((1/8 : ℝ)/p)))

theorem spectralWeberKClosed_continuousAt (ν : ℂ) {p : ℝ} (hp : 0 < p) :
    ContinuousAt (spectralWeberKClosed ν) p := by
  have harg : ContinuousAt (fun q : ℝ => (1/8 : ℝ)/q) p :=
    continuousAt_const.div continuousAt_id hp.ne'
  have hpos : 0 < (1/8 : ℝ)/p := div_pos (by norm_num) hp
  have hK := (schlafliBesselK_hasDerivAt ν _ hpos).continuousAt.comp harg
  have hpow : ContinuousAt (fun q : ℝ => (q : ℂ)^(-(1/2 : ℂ))) p :=
    (by fun_prop : ContinuousAt (fun q : ℝ => (q : ℂ)) p).cpow continuousAt_const
      (Complex.ofReal_mem_slitPlane.mpr hp)
  have he : ContinuousAt (fun q : ℝ => Complex.exp (((1/8 : ℝ)/q : ℝ) : ℂ)) p := by
    apply Complex.continuous_exp.continuousAt.comp
    exact Complex.continuous_ofReal.continuousAt.comp harg
  exact (hpow.mul (he.mul hK)).const_mul _

theorem spectralWeberKClosed_mellin_scale (ν s : ℂ) :
    mellin (spectralWeberKClosed ν) s =
      ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
        ((1/8 : ℂ)^(s-1/2)*
          mellin (fun x : ℝ => Complex.exp (x : ℂ)*schlafliBesselK ν x) (1/2-s)) := by
  unfold spectralWeberKClosed
  rw [show (fun p : ℝ =>
    ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))*
      ((p : ℂ)^(-(1/2 : ℂ))*(Complex.exp (((1/8 : ℝ)/p : ℝ) : ℂ)*schlafliBesselK ν ((1/8 : ℝ)/p)))) =
    (fun p : ℝ => ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν))) •
      ((p : ℂ)^(-(1/2 : ℂ))*(Complex.exp (((1/8 : ℝ)/p : ℝ) : ℂ)*schlafliBesselK ν ((1/8 : ℝ)/p)))) by rfl]
  rw [mellin_const_smul,spectral_mellin_cpow_comp_div
    (fun x : ℝ => Complex.exp (x : ℂ)*schlafliBesselK ν x) (by norm_num)]
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  rw [show s+(-(1/2 : ℂ)) = s-1/2 by ring,show -(s-(1/2 : ℂ)) = 1/2-s by ring]
  rfl

theorem spectralWeberKClosed_mellin_convergent (ν s : ℂ) (hs : 0 < s.re)
    (hstrip : s.re+|ν.re| < 1/2) :
    MellinConvergent (spectralWeberKClosed ν) s := by
  have hleft : |ν.re| < ((1/2 : ℂ)-s).re := by norm_num; linarith
  have hright : ((1/2 : ℂ)-s).re < 1/2 := by norm_num; linarith
  have hA := (spectralAntiK_hasMellin ν (1/2-s) hleft hright).1
  have hinner := (spectral_mellinConvergent_cpow_comp_div
    (fun x : ℝ => Complex.exp (x : ℂ)*schlafliBesselK ν x)
    (b := (1/8 : ℝ)) (by norm_num) (-(1/2 : ℂ)) s).mpr
      (by simpa only [show -(s+(-(1/2 : ℂ))) = 1/2-s by ring] using hA)
  simpa only [spectralWeberKClosed,smul_eq_mul] using! hinner.const_smul
    ((Real.sqrt Real.pi : ℂ)/(4*Complex.cos ((Real.pi : ℂ)*ν)))

end ArtinMatthews
