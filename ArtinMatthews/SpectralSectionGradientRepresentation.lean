module

public import ArtinMatthews.SpectralSectionWeakPairing
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual frame gradient of a hyperbolic section agrees with the
coordinate derivatives of any genuine smooth plane representative. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace ArtinMatthews

theorem h2SectionGradient_representation (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ)
    (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) (i : Fin 2) :
    h2SectionGradient F z i =
      z.im • fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i) := by
  have he' : (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (z : ℂ)]
      (fun w : ℂ => φ (Complex.equivRealProdCLM w)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.im_pos] with w hw
    have hh := he (UpperHalfPlane.ofComplex w)
    simpa only [UpperHalfPlane.ofComplex_apply_of_im_pos hw,
      Complex.equivRealProdCLM_apply, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im] using hh.symm
  have hd : fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) (z : ℂ) =
      (fderiv ℝ φ (z.re,z.im)).comp Complex.equivRealProdCLM.toContinuousLinearMap := by
    rw [he'.fderiv_eq]
    change fderiv ℝ (φ ∘ Complex.equivRealProdCLM) (z : ℂ) = _
    rw [fderiv_comp (z : ℂ) (hφ.differentiable (by simp) _) Complex.equivRealProdCLM.differentiableAt,
      Complex.equivRealProdCLM.fderiv]
    rfl
  fin_cases i <;> simp [h2SectionGradient,spectralPlaneDirection,hd,
    ContinuousLinearMap.comp_apply,Complex.equivRealProdCLM_apply]

end ArtinMatthews
