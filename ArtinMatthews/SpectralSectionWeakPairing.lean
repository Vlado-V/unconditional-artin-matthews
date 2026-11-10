module

public import ArtinMatthews.SpectralSectionPlaneSmoothExtension
public import ArtinMatthews.SpectralSectionGradient
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import ArtinMatthews.SpectralHyperbolicWeakPairing
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual positive-half-plane section and its actual frame gradient
satisfy the weak pairing, using a proved smooth extension only below the
compact test support. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace ArtinMatthews

def spectralPlaneDirection (i : Fin 2) : ℝ × ℝ := ![(1,0),(0,1)] i

theorem spectralSectionSmoothExtension_fderiv {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) {p : ℝ × ℝ} (hp : Y < p.2) (v : ℝ × ℝ) :
    fderiv ℝ (spectralSectionSmoothExtension Y F) p v =
      fderiv ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
        (Complex.equivRealProdCLM.symm p) (Complex.equivRealProdCLM.symm v) := by
  have he : spectralSectionSmoothExtension Y F =ᶠ[𝓝 p] spectralSectionPlane F := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    exact spectralSectionSmoothExtension_eq hY F hq.le
  rw [he.fderiv_eq]
  have hpos : 0 < (Complex.equivRealProdCLM.symm p).im := by
    simpa [Complex.equivRealProdCLM_symm_apply] using hY.trans hp
  have hf : DifferentiableAt ℝ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      (Complex.equivRealProdCLM.symm p) :=
    (hF.contDiffAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hpos)).differentiableAt (by simp)
  change fderiv ℝ ((fun w : ℂ => F (UpperHalfPlane.ofComplex w)) ∘
    Complex.equivRealProdCLM.symm) p v = _
  rw [fderiv_comp p hf Complex.equivRealProdCLM.symm.differentiableAt,
    Complex.equivRealProdCLM.symm.fderiv]
  rfl

theorem spectralSectionSmoothExtension_frame {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im}) (z : UpperHalfPlane) (hz : Y < z.im) (i : Fin 2) :
    h2SectionGradient F z i = z.im •
      fderiv ℝ (spectralSectionSmoothExtension Y F) (z.re,z.im) (spectralPlaneDirection i) := by
  rw [spectralSectionSmoothExtension_fderiv hY F hF hz]
  have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
    Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
  rw [hc]
  fin_cases i <;> simp [h2SectionGradient,spectralPlaneDirection,
    Complex.equivRealProdCLM_symm_apply]

/-- The weak derivative is the literal actual frame gradient of the section;
no independent weak-gradient witness occurs in the hypotheses. -/
theorem h2_section_weak_pairing {Y : ℝ} (hY : 0 < Y)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    (φ : ℝ × ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ)
    (hheight : tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2}) (i : Fin 2) :
    (∫ z : UpperHalfPlane, z.im^2 •
      (F z * fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i))) =
      -∫ z : UpperHalfPlane, h2SectionGradient F z i * (z.im • φ (z.re,z.im)) := by
  have h := h2_plane_weak_pairing (spectralSectionSmoothExtension Y F) φ
    (spectralSectionSmoothExtension_contDiff hY F hF) hφ hs
    (fun p hp => hY.trans (hheight hp)) (spectralPlaneDirection i)
  have hzero {z : UpperHalfPlane} (hz : ¬ Y < z.im) : φ (z.re,z.im) = 0 :=
    image_eq_zero_of_notMem_tsupport (fun ht => hz (hheight ht))
  have hDzero {z : UpperHalfPlane} (hz : ¬ Y < z.im) :
      fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun p => fderiv ℝ φ p (spectralPlaneDirection i))
      (fun ht => hz (hheight (tsupport_fderiv_apply_subset ℝ (spectralPlaneDirection i) ht)))
  have hleft : (fun z : UpperHalfPlane => z.im^2 •
      (spectralSectionSmoothExtension Y F (z.re,z.im) *
        fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i))) =
      (fun z : UpperHalfPlane => z.im^2 •
        (F z * fderiv ℝ φ (z.re,z.im) (spectralPlaneDirection i))) := by
    funext z
    by_cases hz : Y < z.im
    · rw [spectralSectionSmoothExtension_at_upper hY F z hz.le]
    · rw [hDzero hz,mul_zero,mul_zero]
  have hright : (fun z : UpperHalfPlane =>
      (z.im • fderiv ℝ (spectralSectionSmoothExtension Y F) (z.re,z.im)
        (spectralPlaneDirection i)) * (z.im • φ (z.re,z.im))) =
      (fun z : UpperHalfPlane => h2SectionGradient F z i * (z.im • φ (z.re,z.im))) := by
    funext z
    by_cases hz : Y < z.im
    · rw [spectralSectionSmoothExtension_frame hY F hF z hz i]
    · rw [hzero hz,smul_zero,mul_zero,mul_zero]
  rw [hleft,hright] at h
  exact h

end ArtinMatthews
