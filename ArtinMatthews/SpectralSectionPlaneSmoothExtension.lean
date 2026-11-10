module

public import ArtinMatthews.SpectralCoreLocalization
public import ArtinMatthews.SpectralCoreLocalizationDerivatives
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

/-! A genuine globally smooth plane extension of a hyperbolic section,
agreeing with the section and its horizontal derivative above a fixed
positive height. -/

namespace ArtinMatthews
noncomputable section

open Set Filter
open scoped Topology ContDiff

def spectralHeightTransition (Y y : ℝ) : ℝ := Real.smoothTransition (2*y/Y-1)

def spectralSectionSmoothExtension (Y : ℝ) (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ :=
  (spectralHeightTransition Y p.2 : ℂ)*spectralSectionPlane F p

theorem spectralSectionPlane_at_upper (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralSectionPlane F (z.re,z.im) = F z := by
  have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
    Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
  simp only [spectralSectionPlane, hc, UpperHalfPlane.ofComplex_apply]

theorem spectralHeightTransition_zero {Y y : ℝ} (hY : 0 < Y) (hy : y ≤ Y/2) :
    spectralHeightTransition Y y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hh : 2*y/Y ≤ 1 := (div_le_one hY).mpr (by linarith)
  linarith

theorem spectralHeightTransition_one {Y y : ℝ} (hY : 0 < Y) (hy : Y ≤ y) :
    spectralHeightTransition Y y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hh : 2 ≤ 2*y/Y := (le_div_iff₀ hY).mpr (by linarith)
  linarith

theorem spectralSectionSmoothExtension_zero {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : p.2 ≤ Y/2) :
    spectralSectionSmoothExtension Y F p = 0 := by
  simp only [spectralSectionSmoothExtension, spectralHeightTransition_zero hY hp,
    Complex.ofReal_zero, zero_mul]

theorem spectralSectionSmoothExtension_eq {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : Y ≤ p.2) :
    spectralSectionSmoothExtension Y F p = spectralSectionPlane F p := by
  simp only [spectralSectionSmoothExtension, spectralHeightTransition_one hY hp,
    Complex.ofReal_one, one_mul]

theorem spectralSectionSmoothExtension_contDiff {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : ContDiff ℝ ∞ (spectralSectionSmoothExtension Y F) := by
  have hχ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (spectralHeightTransition Y p.2 : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp
      (Real.smoothTransition.contDiff.comp (by fun_prop))
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : 0 < p.2
  · exact hχ.contDiffAt.mul (spectralSectionPlane_contDiffAt F hF hp)
  · have hlow : p.2 < Y/2 := by linarith
    have he : spectralSectionSmoothExtension Y F =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hlow] with q hq
      exact spectralSectionSmoothExtension_zero hY F hq.le
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem spectralSectionSmoothExtension_partialX {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) {p : ℝ × ℝ} (hp : Y ≤ p.2) :
    spectralPlanePartialX (spectralSectionSmoothExtension Y F) p =
      spectralPlanePartialX (spectralSectionPlane F) p := by
  have he : (fun t : ℝ => spectralSectionSmoothExtension Y F (t,p.2)) =
      (fun t : ℝ => spectralSectionPlane F (t,p.2)) :=
    funext (fun _ => spectralSectionSmoothExtension_eq hY F hp)
  exact congrArg (fun g : ℝ → ℂ => deriv g p.1) he

theorem spectralSectionSmoothExtension_partialX_eq_fderiv {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {p : ℝ × ℝ} (hp : Y ≤ p.2) :
    spectralPlanePartialX (spectralSectionSmoothExtension Y F) p =
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
        (Complex.equivRealProdCLM.symm p) 1 := by
  rw [spectralSectionSmoothExtension_partialX hY F hp]
  exact (spectralSectionPlane_coordinate_derivatives F hF (hY.trans_le hp)).1

theorem spectralSectionSmoothExtension_at_upper {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) (hz : Y ≤ z.im) :
    spectralSectionSmoothExtension Y F (z.re,z.im) = F z := by
  rw [spectralSectionSmoothExtension_eq hY F hz, spectralSectionPlane_at_upper]

end
end ArtinMatthews
