module

public import ArtinMatthews.SpectralSectionPlaneSmoothExtension
public import ArtinMatthews.SpectralCuspGraphCompletion
import ArtinMatthews.SpectralCoreLocalizationCoordinates
public import ArtinMatthews.SpectralSectionEnergy
public import ArtinMatthews.SpectralCoreLocalizationDerivatives
public import ArtinMatthews.SpectralHyperbolicCoordinates
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
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

/-! Finite actual hyperbolic energy supplies the cusp graph's horizontal energy. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff

namespace ArtinMatthews

theorem spectralSectionSmoothExtension_cusp_energy (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun v : ℂ => F (UpperHalfPlane.ofComplex v))
      {v : ℂ | 0 < v.im}) {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (h2SectionEnergy F) (hyperbolicCuspStrip w Y)) :
    IntegrableOn (cuspHorizontalEnergy (spectralSectionSmoothExtension Y F) w) (Ioi Y) ∧
    (∫ y in Ioi Y, cuspHorizontalEnergy (spectralSectionSmoothExtension Y F) w y) ≤
      ∫ z in hyperbolicCuspStrip w Y, h2SectionEnergy F z := by
  let G := spectralSectionSmoothExtension Y F
  let E : ℝ × ℝ → ℝ := fun p =>
    h2SectionEnergy F (UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p))
  let S : Set (ℝ × ℝ) := (Ioc 0 w) ×ˢ (Ioi Y)
  have hS : MeasurableSet S := measurableSet_Ioc.prod measurableSet_Ioi
  have hpos : S ⊆ {p : ℝ × ℝ | 0 < p.2} := fun _ hp => hY.trans hp.2
  have he (z : UpperHalfPlane) : E (z.re,z.im) = h2SectionEnergy F z := by
    have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
      Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
    simp only [E,hc,UpperHalfPlane.ofComplex_apply]
  have hi : IntegrableOn (fun p => E p / p.2^2) S := by
    apply (upperHalfPlane_integrableOn_coordinates E hS hpos).mp
    simpa only [he,S,hyperbolicCuspStrip,mem_prod,mem_Ioi] using henergy
  have hpoint (p : ℝ × ℝ) (hp : p ∈ S) :
      ‖spectralPlanePartialX G p‖^2 ≤ E p / p.2^2 := by
    have hy : Y ≤ p.2 := hp.2.le
    rw [spectralSectionSmoothExtension_partialX hY F hy]
    dsimp only [E]
    rw [spectralSectionPlane_energy F hF (hpos hp),mul_div_cancel_left₀ _
      (pow_ne_zero 2 (ne_of_gt (hpos hp)))]
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hG := spectralSectionSmoothExtension_contDiff hY F hF
  have hD : IntegrableOn (fun p => ‖spectralPlanePartialX G p‖^2) S := by
    apply hi.mono' ((spectralPlanePartialX_continuous hG).norm.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hS] with p hp
    change ‖‖spectralPlanePartialX G p‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpoint p hp
  have hprod : Integrable (fun p => ‖spectralPlanePartialX G p‖^2)
      ((volume.restrict (Ioc 0 w)).prod (volume.restrict (Ioi Y))) := by
    change Integrable _ ((volume.prod volume).restrict S) at hD
    rw [← Measure.prod_restrict] at hD
    exact hD
  have hhorizontal : (fun y => ∫ x in Ioc 0 w, ‖spectralPlanePartialX G (x,y)‖^2) =
      cuspHorizontalEnergy G w := by
    funext y
    simp only [cuspHorizontalEnergy,spectralPlanePartialX,intervalIntegral.integral_of_le hw.le]
  refine ⟨?_,?_⟩
  · simpa only [hhorizontal,IntegrableOn,G] using hprod.integral_prod_right
  · have htotal : (∫ z in hyperbolicCuspStrip w Y, h2SectionEnergy F z) =
        ∫ p in S, E p / p.2^2 := by
      simpa only [he,S,hyperbolicCuspStrip,mem_prod,mem_Ioi] using
        upperHalfPlane_setIntegral_coordinates E hS hpos
    rw [htotal]
    calc
      _ = ∫ p in S, ‖spectralPlanePartialX G p‖^2 := by
        change _ = ∫ p, ‖spectralPlanePartialX G p‖^2 ∂(volume.prod volume).restrict S
        rw [← Measure.prod_restrict,integral_prod_symm _ hprod,hhorizontal]
      _ ≤ ∫ p in S, E p / p.2^2 := by
        apply integral_mono_ae hD hi
        filter_upwards [ae_restrict_mem hS] with p hp
        exact hpoint p hp

/-- A smooth section of finite actual energy produces a genuine generator
of the cusp derivative graph, with no auxiliary integrability premise. -/
def spectralSectionCuspSmoothCore (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun v : ℂ => F (UpperHalfPlane.ofComplex v))
      {v : ℂ | 0 < v.im}) {w Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (henergy : IntegrableOn (h2SectionEnergy F) (hyperbolicCuspStrip w Y)) :
    SpectralCuspSmoothCore w Y where
  toFun := spectralSectionSmoothExtension Y F
  smooth := spectralSectionSmoothExtension_contDiff hY F hF
  energy_integrable := (spectralSectionSmoothExtension_cusp_energy F hF hw hY henergy).1

end ArtinMatthews
