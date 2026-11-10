module

public import ArtinMatthews.SpectralBesselI
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselConnectionGamma
public import ArtinMatthews.SpectralBesselIContinuity
public import ArtinMatthews.SpectralBesselKEquation
public import ArtinMatthews.SpectralDampedIMellin
public import ArtinMatthews.SpectralDampedKMellin
public import ArtinMatthews.SpectralMellinUniqueness
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual K/I connection follows from the proved damped Mellin
integrals and uniqueness.  It includes zero order without division by sin(pi nu). -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralDampedI_hasMellin (ν s : ℂ)
    (hν : -(1/2 : ℝ) < ν.re) (hleft : 0 < (s+ν).re) (hright : s.re < 1/2) :
    HasMellin (fun x : ℝ => Complex.exp (-(x : ℂ))*spectralBesselI ν x) s
      ((2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (1/2-s)/
        ((Real.sqrt Real.pi : ℂ)*Complex.Gamma (ν+1-s))) := by
  constructor
  · simpa only [MellinConvergent,smul_eq_mul,mul_assoc] using
      spectralDampedI_mellin_integrable ν s hν hleft hright
  · simpa only [mellin,smul_eq_mul,mul_assoc] using
      spectralDampedI_mellin ν s hν hleft hright

theorem spectralDampedK_hasMellin (ν s : ℂ) (hs : |ν.re| < s.re) :
    HasMellin (fun x : ℝ => Complex.exp (-(x : ℂ))*schlafliBesselK ν x) s
      ((Real.sqrt Real.pi : ℂ)*(2 : ℂ)^(-s)*Complex.Gamma (s+ν)*Complex.Gamma (s-ν)/
        Complex.Gamma (s+1/2)) := by
  constructor
  · simpa only [MellinConvergent,smul_eq_mul,mul_assoc] using
      spectralDampedK_mellin_integrable ν s hs
  · simpa only [mellin,smul_eq_mul,mul_assoc] using spectralDampedK_mellin ν s hs

private theorem mellin_value_sub {f g : ℝ → ℂ} {s a b : ℂ}
    (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (fun x => f x-g x) s (a-b) := by
  refine ⟨(hasMellin_sub hf.1 hg.1).1,?_⟩
  rw [(hasMellin_sub hf.1 hg.1).2,hf.2,hg.2]

private theorem mellin_value_mul {f : ℝ → ℂ} {s a : ℂ}
    (hf : HasMellin f s a) (c : ℂ) :
    HasMellin (fun x => c*f x) s (c*a) := by
  constructor
  · simpa only [smul_eq_mul] using hf.1.const_smul c
  · simpa only [smul_eq_mul,hf.2] using mellin_const_smul f s c

theorem schlafliBesselK_eq_I_difference {ν : ℂ} (hν : |ν.re| < 1/2)
    {x : ℝ} (hx : 0 < x) :
    Complex.sin ((Real.pi : ℂ)*ν)*schlafliBesselK ν x =
      ((Real.pi : ℂ)/2)*(spectralBesselI (-ν) x-spectralBesselI ν x) := by
  let f : ℝ → ℂ := fun y =>
    ((Real.pi : ℂ)/2)*(Complex.exp (-(y : ℂ))*spectralBesselI (-ν) y-
      Complex.exp (-(y : ℂ))*spectralBesselI ν y)-
    Complex.sin ((Real.pi : ℂ)*ν)*(Complex.exp (-(y : ℂ))*schlafliBesselK ν y)
  have hnp : -(1/2 : ℝ) < ν.re := by linarith [neg_le_abs ν.re]
  have hnm : -(1/2 : ℝ) < (-ν).re := by simp only [Complex.neg_re]; linarith [le_abs_self ν.re]
  have hline (s : ℂ) (hs : |ν.re| < s.re) (hsh : s.re < 1/2) : HasMellin f s 0 := by
    have hsp : 0 < (s+ν).re := by simp only [Complex.add_re]; linarith [neg_le_abs ν.re]
    have hsm : 0 < (s+(-ν)).re := by
      simp only [Complex.add_re,Complex.neg_re]
      linarith [le_abs_self ν.re]
    have hp := spectralDampedI_hasMellin ν s hnp hsp hsh
    have hm := spectralDampedI_hasMellin (-ν) s hnm hsm hsh
    have hk := spectralDampedK_hasMellin ν s hs
    have hh := mellin_value_sub
      (mellin_value_mul (mellin_value_sub hm hp) ((Real.pi : ℂ)/2))
      (mellin_value_mul hk (Complex.sin ((Real.pi : ℂ)*ν)))
    have hv := spectralBesselConnection_gamma ν s hs hsh
    simpa only [f,← sub_eq_add_neg,hv,sub_self] using hh
  let σ : ℝ := (|ν.re|+1/2)/2
  have hσ : |ν.re| < σ := by dsimp [σ]; linarith
  have hσh : σ < 1/2 := by dsimp [σ]; linarith
  have hconv : MellinConvergent f σ :=
    (hline (σ : ℂ) (by simpa using hσ) (by simpa using hσh)).1
  have hzero (t : ℝ) : mellin f ((σ : ℂ)+t*Complex.I) = 0 :=
    (hline _ (by simpa using hσ) (by simpa using hσh)).2
  have hc : ContinuousAt f x := by
    dsimp [f]
    exact ((Complex.continuous_exp.continuousAt.comp (by fun_prop)).mul
      (spectralBesselI_continuousAt (-ν) hx) |>.sub
      ((Complex.continuous_exp.continuousAt.comp (by fun_prop)).mul
        (spectralBesselI_continuousAt ν hx))).const_mul _ |>.sub
      (((Complex.continuous_exp.continuousAt.comp (by fun_prop)).mul
        (schlafliBesselK_hasDerivAt ν x hx).continuousAt).const_mul _)
  have hz := spectral_mellin_zero_of_vertical_zero f σ hconv hzero hx hc
  have he : Complex.exp (-(x : ℂ))*
      (((Real.pi : ℂ)/2)*(spectralBesselI (-ν) x-spectralBesselI ν x)) =
      Complex.exp (-(x : ℂ))*(Complex.sin ((Real.pi : ℂ)*ν)*schlafliBesselK ν x) := by
    dsimp [f] at hz
    linear_combination hz
  exact (mul_left_cancel₀ (Complex.exp_ne_zero _) he).symm

end ArtinMatthews
