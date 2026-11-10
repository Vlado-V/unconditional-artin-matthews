module

public import ArtinMatthews.SpectralBesselHyperbolicEvaluation
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import ArtinMatthews.SpectralFourierSecondDerivativeDecay
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

/-! The actual cosh exponential and two integrable derivatives. Absolute
convergence is deduced from the already proved arbitrary-order K kernels. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology FourierTransform

namespace ArtinMatthews

def spectralKLCoshExponential (x u : ℝ) : ℂ := Complex.exp (-(x*Real.cosh u) : ℝ)

def spectralKLCoshExponentialD1 (x u : ℝ) : ℂ :=
  spectralKLCoshExponential x u*((-x*Real.sinh u : ℝ) : ℂ)

def spectralKLCoshExponentialD2 (x u : ℝ) : ℂ :=
  spectralKLCoshExponential x u*((x^2*(Real.sinh u)^2-x*Real.cosh u : ℝ) : ℂ)

theorem spectralKLCoshExponential_hasDerivAt (x u : ℝ) :
    HasDerivAt (spectralKLCoshExponential x) (spectralKLCoshExponentialD1 x u) u := by
  have hd := (((Real.hasDerivAt_cosh u).const_mul (-x)).ofReal_comp).cexp
  simpa only [spectralKLCoshExponential,spectralKLCoshExponentialD1,neg_mul] using! hd

theorem spectralKLCoshExponentialD1_hasDerivAt (x u : ℝ) :
    HasDerivAt (spectralKLCoshExponentialD1 x) (spectralKLCoshExponentialD2 x u) u := by
  have hd := (spectralKLCoshExponential_hasDerivAt x u).mul
    (((Real.hasDerivAt_sinh u).const_mul (-x)).ofReal_comp)
  convert! hd using 1
  dsimp [spectralKLCoshExponentialD1,spectralKLCoshExponentialD2]
  push_cast
  ring

theorem spectralKLCoshExponential_deriv (x : ℝ) :
    deriv (spectralKLCoshExponential x) = spectralKLCoshExponentialD1 x := by
  funext u
  exact (spectralKLCoshExponential_hasDerivAt x u).deriv

theorem spectralKLCoshExponentialD1_deriv (x : ℝ) :
    deriv (spectralKLCoshExponentialD1 x) = spectralKLCoshExponentialD2 x := by
  funext u
  exact (spectralKLCoshExponentialD1_hasDerivAt x u).deriv

theorem spectralKLCoshExponential_cosh_pair (ν : ℂ) (x u : ℝ) :
    spectralKLCoshExponential x u*Complex.cosh (ν*(u : ℂ)) =
      (spectralKLogKernel ν x u+spectralKLogKernel (-ν) x u)/2 := by
  simp only [spectralKLCoshExponential,spectralKLogKernel,Complex.cosh,Complex.exp_add,neg_mul]
  ring

theorem spectralKLCoshExponential_sinh_pair (ν : ℂ) (x u : ℝ) :
    spectralKLCoshExponential x u*Complex.sinh (ν*(u : ℂ)) =
      (spectralKLogKernel ν x u-spectralKLogKernel (-ν) x u)/2 := by
  simp only [spectralKLCoshExponential,spectralKLogKernel,Complex.sinh,Complex.exp_add,neg_mul]
  ring

theorem spectralKLCoshExponential_mul_cosh_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => spectralKLCoshExponential x u*Complex.cosh (ν*(u : ℂ))) := by
  apply (((spectralKLogKernel_integrable ν hx).add (spectralKLogKernel_integrable (-ν) hx)).div_const 2).congr
  filter_upwards with u
  exact (spectralKLCoshExponential_cosh_pair ν x u).symm

theorem spectralKLCoshExponential_mul_sinh_integrable (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => spectralKLCoshExponential x u*Complex.sinh (ν*(u : ℂ))) := by
  apply (((spectralKLogKernel_integrable ν hx).sub (spectralKLogKernel_integrable (-ν) hx)).div_const 2).congr
  filter_upwards with u
  exact (spectralKLCoshExponential_sinh_pair ν x u).symm

theorem spectralKLCoshExponential_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (spectralKLCoshExponential x) := by
  simpa only [zero_mul,Complex.cosh_zero,mul_one] using spectralKLCoshExponential_mul_cosh_integrable 0 hx

theorem spectralKLCoshExponentialD1_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (spectralKLCoshExponentialD1 x) := by
  apply ((spectralKLCoshExponential_mul_sinh_integrable 1 hx).const_mul (-(x : ℂ))).congr
  filter_upwards with u
  simp only [spectralKLCoshExponentialD1,one_mul,← Complex.ofReal_sinh]
  push_cast
  ring

theorem spectralKLCoshExponentialD2_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (spectralKLCoshExponentialD2 x) := by
  have hC2 := (spectralKLCoshExponential_mul_cosh_integrable 2 hx).const_mul ((x : ℂ)^2/2)
  have hC0 := (spectralKLCoshExponential_integrable hx).const_mul ((x : ℂ)^2/2)
  have hC1 := (spectralKLCoshExponential_mul_cosh_integrable 1 hx).const_mul (x : ℂ)
  apply ((hC2.sub hC0).sub hC1).congr
  filter_upwards with u
  have hsq : (Real.sinh u)^2 = (Real.cosh (2*u)-1)/2 := by
    nlinarith [Real.cosh_two_mul u,Real.cosh_sq_sub_sinh_sq u]
  simp only [Pi.sub_apply,spectralKLCoshExponentialD2,one_mul]
  rw [show (2 : ℂ)*(u : ℂ) = ((2*u : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_cosh,← Complex.ofReal_cosh,hsq]
  push_cast
  ring

theorem spectralKLCoshExponential_fourier_integrable {x : ℝ} (hx : 0 < x) :
    Integrable (𝓕 (spectralKLCoshExponential x)) := by
  apply spectral_fourier_integrable_of_two_derivatives
  · exact spectralKLCoshExponential_integrable hx
  · intro u
    exact (spectralKLCoshExponential_hasDerivAt x u).differentiableAt
  · rw [spectralKLCoshExponential_deriv]
    exact spectralKLCoshExponentialD1_integrable hx
  · rw [spectralKLCoshExponential_deriv]
    intro u
    exact (spectralKLCoshExponentialD1_hasDerivAt x u).differentiableAt
  · rw [spectralKLCoshExponential_deriv,spectralKLCoshExponentialD1_deriv]
    exact spectralKLCoshExponentialD2_integrable hx

end ArtinMatthews
