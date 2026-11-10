module

public import ArtinMatthews.SpectralSeparableTestSeed
public import Mathlib.Order.CompletePartialOrder
public import ArtinMatthews.SpectralSeparableLaplacian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Real compact period-window and vertical tests give literal complex
hyperbolic seeds, with the real one-dimensional derivatives and signs made
explicit for the weak constant-term equation. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem spectral_deriv_ofReal (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    deriv (fun t => (f t : ℂ)) x = ((deriv f x : ℝ) : ℂ) :=
  (hf x).hasDerivAt.ofReal_comp.deriv

theorem spectral_second_deriv_ofReal (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    deriv (deriv (fun t => (f t : ℂ))) x = ((deriv (deriv f) x : ℝ) : ℂ) := by
  have he : deriv (fun t => (f t : ℂ)) = fun t => ((deriv f t : ℝ) : ℂ) :=
    funext (spectral_deriv_ofReal f (hf.differentiable (by simp)))
  rw [he]
  exact spectral_deriv_ofReal (deriv f)
    ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp)) x

def h2RealSeparableSmoothSeed (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  h2SeparableSmoothSeed (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (Complex.ofRealCLM.contDiff.comp hχ) (Complex.ofRealCLM.contDiff.comp hη)
    (hcχ.comp_left Complex.ofReal_zero) (hcη.comp_left Complex.ofReal_zero)
    ((tsupport_comp_subset Complex.ofReal_zero η).trans hpos)

theorem h2RealSeparableSmoothSeed_apply (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z = (χ z.re * η z.im : ℝ) := by
  change (χ z.re : ℂ) * (η z.im : ℂ) = _
  exact Complex.ofReal_mul _ _ |>.symm

theorem h2RealSeparableSmoothSeed_laplacian (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z =
      ((-(z.im^2) * (deriv (deriv χ) z.re * η z.im + χ z.re * deriv (deriv η) z.im) : ℝ) : ℂ) := by
  change h2SectionPositiveLaplacian
    (fun w : UpperHalfPlane => (χ w.re : ℂ) * (η w.im : ℂ)) z = _
  have hχc : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hηc : ContDiff ℝ ∞ (fun y => (η y : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  rw [h2SectionPositiveLaplacian_separable (fun x => (χ x : ℂ))
    (fun y => (η y : ℂ)) hχc hηc]
  simp only [spectral_second_deriv_ofReal χ hχ,spectral_second_deriv_ofReal η hη,
    Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_add]

end ArtinMatthews
