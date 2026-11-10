module

public import ArtinMatthews.SpectralRealSeparableLaplacian
public import ArtinMatthews.SpectralSectionGradientRepresentation
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

/-! Exact frame derivatives of the actual separable compact tests used to
identify weak horizontal means and their genuine vertical derivative. -/

noncomputable section
open Set
open scoped ContDiff

namespace ArtinMatthews

theorem h2SeparableSmoothSeed_gradient_zero (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 0 =
      z.im • (deriv χ z.re * η z.im) := by
  rw [h2SectionGradient_representation
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => χ p.1 * η p.2) (z.re,z.im) (1,0) = _
  rw [spectralPlane_fderiv_separable_x χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]

theorem h2SeparableSmoothSeed_gradient_one (χ η : ℝ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 1 =
      z.im • (χ z.re * deriv η z.im) := by
  rw [h2SectionGradient_representation
    (h2SeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val (fun p : ℝ × ℝ => χ p.1 * η p.2)
    ((hχ.comp contDiff_fst).mul (hη.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => χ p.1 * η p.2) (z.re,z.im) (0,1) = _
  rw [spectralPlane_fderiv_separable_y χ η (hχ.differentiable (by simp)) (hη.differentiable (by simp))]

theorem h2RealSeparableSmoothSeed_gradient_zero (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 0 =
      ((z.im * (deriv χ z.re * η z.im) : ℝ) : ℂ) := by
  have hχc : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hηc : ContDiff ℝ ∞ (fun y => (η y : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  rw [h2SectionGradient_representation
    (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val
    (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ))
    ((hχc.comp contDiff_fst).mul (hηc.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) (z.re,z.im) (1,0) = _
  rw [spectralPlane_fderiv_separable_x (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (hχc.differentiable (by simp)) (hηc.differentiable (by simp))]
  simp only [spectral_deriv_ofReal χ (hχ.differentiable (by simp)),
    Complex.real_smul,Complex.ofReal_mul]

theorem h2RealSeparableSmoothSeed_gradient_one (χ η : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hη : ContDiff ℝ ∞ η)
    (hcχ : HasCompactSupport χ) (hcη : HasCompactSupport η)
    (hpos : tsupport η ⊆ Ioi (0 : ℝ)) (z : UpperHalfPlane) :
    h2SectionGradient (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val z 1 =
      ((z.im * (χ z.re * deriv η z.im) : ℝ) : ℂ) := by
  have hχc : ContDiff ℝ ∞ (fun x => (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  have hηc : ContDiff ℝ ∞ (fun y => (η y : ℂ)) := Complex.ofRealCLM.contDiff.comp hη
  rw [h2SectionGradient_representation
    (h2RealSeparableSmoothSeed χ η hχ hη hcχ hcη hpos).val
    (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ))
    ((hχc.comp contDiff_fst).mul (hηc.comp contDiff_snd)) (fun _ => rfl)]
  change z.im • fderiv ℝ (fun p : ℝ × ℝ => (χ p.1 : ℂ) * (η p.2 : ℂ)) (z.re,z.im) (0,1) = _
  rw [spectralPlane_fderiv_separable_y (fun x => (χ x : ℂ)) (fun y => (η y : ℂ))
    (hχc.differentiable (by simp)) (hηc.differentiable (by simp))]
  simp only [spectral_deriv_ofReal η (hη.differentiable (by simp)),
    Complex.real_smul,Complex.ofReal_mul]

end ArtinMatthews
