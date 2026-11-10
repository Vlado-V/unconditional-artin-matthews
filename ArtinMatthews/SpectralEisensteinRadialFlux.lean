module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact one-dimensional imaginary Green identity for a smooth profile
at real energy, with the hyperbolic vertical density retained. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace ArtinMatthews

def spectralRadialError (ζ : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  -((t:ℂ)^2)*deriv (deriv f) t-ζ*f t

def spectralRadialFlux (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  (inner ℂ (f t) (deriv f t)).im

theorem spectralComplexInner_self_im_zero (a : ℂ) : (inner ℂ a a).im=0 := by
  simp only [RCLike.inner_apply,Complex.mul_conj,Complex.ofReal_im]

theorem spectralRadialFlux_hasDerivAt (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    HasDerivAt (spectralRadialFlux f) (inner ℂ (f t) (deriv (deriv f) t)).im t := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have h0 := ((hf.differentiable (by simp)) t).hasDerivAt
  have h1 := ((hf'.differentiable (by simp)) t).hasDerivAt
  have hi := h0.inner ℂ h1
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hi
  change HasDerivAt (spectralRadialFlux f)
    (inner ℂ (f t) (deriv (deriv f) t)+inner ℂ (deriv f t) (deriv f t)).im t at h
  rwa [Complex.add_im,spectralComplexInner_self_im_zero,add_zero] at h

theorem spectralRadialError_im_density (ζ : ℂ) (hζ : ζ.im=0) (f : ℝ → ℂ)
    {t : ℝ} (ht : 0<t) :
    (((t^2:ℝ)⁻¹) • inner ℂ (f t) (spectralRadialError ζ f t)).im=
      -(inner ℂ (f t) (deriv (deriv f) t)).im := by
  have he : ((t^2:ℝ)⁻¹) • inner ℂ (f t) (spectralRadialError ζ f t)=
      -inner ℂ (f t) (deriv (deriv f) t)-
        ((((t^2:ℝ)⁻¹:ℝ):ℂ)*ζ)*inner ℂ (f t) (f t) := by
    rw [spectralRadialError,inner_sub_right]
    change (t^2:ℝ)⁻¹ • (inner ℂ (f t) ((-((t:ℂ)^2)) • deriv (deriv f) t)-
      inner ℂ (f t) (ζ • f t))=_
    simp only [inner_smul_right,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_pow]
    field_simp [Complex.ofReal_ne_zero.mpr ht.ne']
  have hReal : ((((t^2:ℝ)⁻¹:ℝ):ℂ)*ζ).im=0 := by
    simp only [Complex.mul_im,Complex.ofReal_im,hζ,mul_zero,zero_mul,add_zero]
  rw [he,Complex.sub_im,Complex.neg_im,Complex.mul_im,spectralComplexInner_self_im_zero,hReal,
    mul_zero,zero_mul,add_zero,sub_zero]

theorem spectralRadialError_im_integral (ζ : ℂ) (hζ : ζ.im=0)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) {L U : ℝ} (hL : 0<L) (hLU : L≤U) :
    (∫ t in L..U, ((t^2:ℝ)⁻¹) • inner ℂ (f t) (spectralRadialError ζ f t)).im=
      spectralRadialFlux f L-spectralRadialFlux f U := by
  have hf' := (contDiff_infty_iff_deriv.mp hf).2
  have hf'' := (contDiff_infty_iff_deriv.mp hf').2
  have hE : Continuous (spectralRadialError ζ f) := by
    unfold spectralRadialError
    exact ((Complex.continuous_ofReal.pow 2).neg.mul hf''.continuous).sub
      (continuous_const.mul hf.continuous)
  let G (t : ℝ) := ((t^2:ℝ)⁻¹) • inner ℂ (f t) (spectralRadialError ζ f t)
  have hG : ContinuousOn G (uIcc L U) := by
    have hw : ContinuousOn (fun t : ℝ => (t^2)⁻¹) (uIcc L U) :=
      (continuous_id.pow 2).continuousOn.inv₀ (fun t ht =>
        pow_ne_zero 2 (hL.trans_le ((uIcc_of_le hLU ▸ ht).1)).ne')
    exact hw.smul (hf.continuous.inner hE).continuousOn
  have hGi : IntervalIntegrable G volume L U := hG.intervalIntegrable
  have hd : Continuous (fun t : ℝ => (inner ℂ (f t) (deriv (deriv f) t)).im) :=
    Complex.continuous_im.comp (hf.continuous.inner hf''.continuous)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => spectralRadialFlux_hasDerivAt f hf t) (hd.intervalIntegrable L U)
  change (∫ t in L..U,G t).im=_
  have hIm : (∫ t in L..U,(G t).im)=(∫ t in L..U,G t).im :=
    Complex.imCLM.intervalIntegral_comp_comm hGi
  rw [← hIm]
  calc
    _=∫ t in L..U, -(inner ℂ (f t) (deriv (deriv f) t)).im := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact spectralRadialError_im_density ζ hζ f (hL.trans_le ((uIcc_of_le hLU ▸ ht).1))
    _=_ := by rw [intervalIntegral.integral_neg,hFTC];ring

end ArtinMatthews
