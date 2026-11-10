module

public import ArtinMatthews.SpectralKLHeightPhysicalTest
public import ArtinMatthews.SpectralWeylPhysicalBilinearGaussian
public import ArtinMatthews.SpectralKLMacdonaldSpectralFubini
public import ArtinMatthews.SpectralKLPhysicalDilation
public import ArtinMatthews.SpectralWeylPhysicalContinuity
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

/-! Exact transport of the unregularized physical Weyl pairing back to
its original heights.  The same literal profiles as the native KL input
are used, and the physical measure dx/x is preserved by each dilation. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralKLPhysical_integral_div (F : ℝ → ℂ) :
    (∫ x : ℝ, F x ∂spectralKLPhysicalMeasure) = ∫ x in Ioi (0 : ℝ), F x/(x : ℂ) := by
  rw [spectralKLPhysicalMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
    (by fun_prop) (fun x hx => inv_nonneg.mpr hx.le)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  dsimp only
  rw [Complex.ofReal_inv]
  ring_nf

theorem spectralKLPhysical_measure_dilation_integral (F : ℝ → ℂ) {q : ℝ} (hq : 0 < q) :
    (∫ x : ℝ, F x ∂spectralKLPhysicalMeasure) = ∫ y : ℝ, F (q*y) ∂spectralKLPhysicalMeasure := by
  rw [spectralKLPhysical_integral_div,spectralKLPhysical_integral_div]
  have h := spectralKLPhysical_dilation_integral (fun y : ℝ => F (q*y)) hq
  simpa only [mul_div_cancel₀ _ hq.ne'] using h

theorem spectralKLHeightBaseTest_star (ρ : ℝ → ℝ) (y : ℝ) :
    star (spectralKLHeightBaseTest ρ y) = spectralKLHeightBaseTest ρ y := by
  rw [spectralKLHeightBaseTest,← Complex.ofReal_div]
  exact Complex.conj_ofReal _

theorem spectralKLHeightPhysicalTest_dilation {q : ℝ} (hq : 0 < q) (ρ : ℝ → ℝ) (y : ℝ) :
    spectralKLHeightPhysicalTest q ρ (q*y) = spectralKLHeightBaseTest ρ y := by
  rw [spectralKLHeightPhysicalTest,mul_div_cancel_left₀ _ hq.ne']

theorem spectralWeylPhysicalBilinear_height_dilation {a b X : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (s t : ℝ) (ρ η : ℝ → ℝ)
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hη : Continuous η) (hcη : HasCompactSupport η) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    spectralWeylPhysicalBilinear s t (spectralKLHeightPhysicalTest b η) (spectralKLHeightPhysicalTest a ρ) X =
      ∫ y in Ioi (0 : ℝ), (∫ v in Ioi (0 : ℝ),
        (spectralWeylDimensionlessKernel s t X (a*y) (b*v) : ℂ)*spectralKLHeightBaseTest η v*
          spectralKLHeightBaseTest ρ y/(v : ℂ))/(y : ℂ) := by
  let f := spectralKLHeightPhysicalTest b η
  let g := spectralKLHeightPhysicalTest a ρ
  obtain ⟨hf,hfc,hfp⟩ := spectralKLHeightPhysicalTest_properties hb η hη hcη hpη
  obtain ⟨hg,hgc,hgp⟩ := spectralKLHeightPhysicalTest_properties ha ρ hρ hcρ hpρ
  have hI := spectralWeylPhysicalIntegrand_integrable_of_fold hX s t f g hf.measurable hg.measurable
    (spectralWeylFoldDensity_compact_integrable hX s t f g hf hfc hfp hg hgc hgp)
  change spectralWeylPhysicalBilinear s t f g X = _
  calc
    _ = ∫ x : ℝ, (∫ z : ℝ, spectralWeylPhysicalIntegrand s t f g ((x,z),X)
          ∂spectralKLPhysicalMeasure) ∂spectralKLPhysicalMeasure := integral_prod _ hI
    _ = ∫ y : ℝ, (∫ v : ℝ, (spectralWeylDimensionlessKernel s t X (a*y) (b*v) : ℂ)*
        spectralKLHeightBaseTest η v*spectralKLHeightBaseTest ρ y ∂spectralKLPhysicalMeasure)
          ∂spectralKLPhysicalMeasure := by
      rw [spectralKLPhysical_measure_dilation_integral (fun x => ∫ z : ℝ,
        spectralWeylPhysicalIntegrand s t f g ((x,z),X) ∂spectralKLPhysicalMeasure) ha]
      apply integral_congr_ae
      filter_upwards with y
      rw [spectralKLPhysical_measure_dilation_integral (fun z =>
        spectralWeylPhysicalIntegrand s t f g ((a*y,z),X)) hb]
      apply integral_congr_ae
      filter_upwards with v
      simp only [spectralWeylPhysicalIntegrand,f,g,spectralKLHeightPhysicalTest_dilation ha,
        spectralKLHeightPhysicalTest_dilation hb,spectralKLHeightBaseTest_star]
    _ = _ := by
      rw [spectralKLPhysical_integral_div]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y _
      dsimp only
      rw [spectralKLPhysical_integral_div]

end ArtinMatthews
