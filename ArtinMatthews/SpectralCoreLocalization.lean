module

public import ArtinMatthews.SpectralRellichRectangle
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
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
public import Mathlib.Order.CompletePartialOrder
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

/-! Actual compact localization of a smooth hyperbolic scalar section,
as a Schwartz function on the Cartesian plane. -/

namespace ArtinMatthews
noncomputable section

open Set Filter
open scoped Topology ContDiff

def spectralSectionPlane (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ :=
  F (UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p))

def spectralCoreLocalizationFun (φ : SchwartzMap (ℝ × ℝ) ℂ)
    (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℂ := φ p*spectralSectionPlane F p

theorem spectralCoreLocalizationFun_support (φ : SchwartzMap (ℝ × ℝ) ℂ)
    (F : UpperHalfPlane → ℂ) :
    tsupport (spectralCoreLocalizationFun φ F) ⊆ tsupport φ :=
  tsupport_mul_subset_left

theorem spectralSectionPlane_contDiffAt (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContDiffAt ℝ ∞ (spectralSectionPlane F) p := by
  have hpos : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa only [Complex.equivRealProdCLM_symm_apply, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
      add_zero, zero_add] using hp
  exact (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)).comp p
    Complex.equivRealProdCLM.symm.contDiff.contDiffAt

theorem spectralCoreLocalizationFun_contDiff (φ : SchwartzMap (ℝ × ℝ) ℂ)
    {A a b : ℝ} (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : ContDiff ℝ ∞ (spectralCoreLocalizationFun φ F) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ tsupport φ
  · have hpos : 0 < p.2 := ha.trans_le (hφ hp).2.1
    exact (φ.smooth ⊤).contDiffAt.mul (spectralSectionPlane_contDiffAt F hF hpos)
  · have he : spectralCoreLocalizationFun φ F =ᶠ[𝓝 p] (fun _ => (0 : ℂ)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
      simp only [spectralCoreLocalizationFun, hq, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem spectralCoreLocalizationFun_hasCompactSupport (φ : SchwartzMap (ℝ × ℝ) ℂ)
    {A a b : ℝ} (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (F : UpperHalfPlane → ℂ) : HasCompactSupport (spectralCoreLocalizationFun φ F) :=
  (spectralPlaneRectangle_compact A a b).of_isClosed_subset (isClosed_tsupport _)
    ((spectralCoreLocalizationFun_support φ F).trans hφ)

def spectralCoreLocalization (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) : SchwartzMap (ℝ × ℝ) ℂ :=
  (spectralCoreLocalizationFun_hasCompactSupport φ hφ F).toSchwartzMap
    (spectralCoreLocalizationFun_contDiff φ ha hφ F hF)

theorem spectralCoreLocalization_apply (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (p : ℝ × ℝ) :
    spectralCoreLocalization φ ha hφ F hF p =
      φ p*F (UpperHalfPlane.ofComplex ((p.1 : ℂ)+p.2*Complex.I)) := by
  simp only [spectralCoreLocalization, HasCompactSupport.toSchwartzMap_toFun,
    spectralCoreLocalizationFun, spectralSectionPlane, Complex.equivRealProdCLM_symm_apply]

theorem spectralCoreLocalization_support (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
    (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) :
    tsupport (spectralCoreLocalization φ ha hφ F hF) ⊆ spectralPlaneRectangle A a b :=
  (spectralCoreLocalizationFun_support φ F).trans hφ

end
end ArtinMatthews
