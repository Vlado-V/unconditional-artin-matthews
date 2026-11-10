module

public import ArtinMatthews.SpectralHyperbolicComplexGreen
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

/-! The literal positive H² differential Laplacian of a scalar section,
independent of any choice of smooth plane extension. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff MatrixGroups

namespace ArtinMatthews

def h2SectionPositiveLaplacian (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  spectralPlanePositiveHyperbolic (spectralSectionPlane F) (z.re,z.im)

theorem spectralPlaneSecond_congr_of_eventuallyEq (f g : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (h : f =ᶠ[𝓝 p] g) (i : Fin 2) :
    spectralPlaneSecond f i p = spectralPlaneSecond g i p := by
  have hd : (fun q => fderiv ℝ f q (spectralPlaneDirection i)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (spectralPlaneDirection i)) :=
    h.fderiv.mono (fun q hq => congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (spectralPlaneDirection i)) hq)
  exact congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℂ => A (spectralPlaneDirection i)) hd.fderiv_eq

theorem spectralPlanePositiveHyperbolic_congr_of_eventuallyEq (f g : ℝ × ℝ → ℂ)
    {p : ℝ × ℝ} (h : f =ᶠ[𝓝 p] g) :
    spectralPlanePositiveHyperbolic f p = spectralPlanePositiveHyperbolic g p := by
  unfold spectralPlanePositiveHyperbolic spectralPlanePositiveSecond
  congr 2
  exact Finset.sum_congr rfl (fun i _ => spectralPlaneSecond_congr_of_eventuallyEq f g h i)

theorem spectralSectionPlane_representation_germ (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) : spectralSectionPlane F =ᶠ[𝓝 (z.re,z.im)] φ := by
  filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds z.im_pos] with p hp
  let w := UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p)
  have him : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hp
  have hc : (w.re,w.im) = p := by
    dsimp only [w]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
    exact Complex.equivRealProdCLM.apply_symm_apply p
  rw [← hc,spectralSectionPlane_at_upper,he]

theorem h2SectionPositiveLaplacian_representation (F : UpperHalfPlane → ℂ)
    (φ : ℝ × ℝ → ℂ) (he : ∀ z : UpperHalfPlane, φ (z.re,z.im) = F z)
    (z : UpperHalfPlane) :
    h2SectionPositiveLaplacian F z = spectralPlanePositiveHyperbolic φ (z.re,z.im) :=
  spectralPlanePositiveHyperbolic_congr_of_eventuallyEq _ _
    (spectralSectionPlane_representation_germ F φ he z)

end ArtinMatthews
