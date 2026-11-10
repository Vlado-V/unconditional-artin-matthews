module

public import ArtinMatthews.SpectralCoreLocalization
public import ArtinMatthews.SpectralSectionEnergy
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import ArtinMatthews.SpectralHyperbolicCoordinates
public import ArtinMatthews.SpectralHyperbolicL2
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Actual chart-energy coordinate integrals and their integrability. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set

theorem upperHalfPlane_integrableOn_coordinates (G : ℝ × ℝ → ℝ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => G (z.re,z.im)) {z | (z.re,z.im) ∈ S} ↔
      IntegrableOn (fun p => G p/p.2^2) S := by
  classical
  have h := upperHalfPlane_integrable_coordinates (S.indicator G)
  have hleft : (fun z : UpperHalfPlane => S.indicator G (z.re,z.im)) =
      {z : UpperHalfPlane | (z.re,z.im) ∈ S}.indicator (fun z => G (z.re,z.im)) := by
    funext z
    by_cases hz : (z.re,z.im) ∈ S <;> simp [hz]
  have hright : (fun p : ℝ × ℝ => S.indicator G p/p.2^2) =
      S.indicator (fun p => G p/p.2^2) := by
    funext p
    by_cases hp : p ∈ S <;> simp [hp]
  have hpre : MeasurableSet {z : UpperHalfPlane | (z.re,z.im) ∈ S} :=
    hS.preimage (by fun_prop)
  rw [hleft, integrable_indicator_iff hpre, hright] at h
  change IntegrableOn (fun z : UpperHalfPlane => G (z.re,z.im)) {z | (z.re,z.im) ∈ S} ↔
    Integrable (S.indicator (fun p => G p/p.2^2)) (volume.restrict {p : ℝ × ℝ | 0 < p.2}) at h
  rw [integrable_indicator_iff hS] at h
  simp only [IntegrableOn, Measure.restrict_restrict_of_subset hpositive] at h
  exact h

def spectralCoreChartEnergy (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖spectralSectionPlane F p‖^2+
    h2SectionEnergy F (UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p))

theorem spectralCoreChartEnergy_at_upper (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    spectralCoreChartEnergy F (z.re,z.im) = ‖F z‖^2+h2SectionEnergy F z := by
  have hc : Complex.equivRealProdCLM.symm (z.re,z.im) = (z : ℂ) :=
    Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
  simp only [spectralCoreChartEnergy, spectralSectionPlane, hc, UpperHalfPlane.ofComplex_apply]

theorem spectralCoreChartEnergy_nonneg (F : UpperHalfPlane → ℂ) (p : ℝ × ℝ) :
    0 ≤ spectralCoreChartEnergy F p :=
  add_nonneg (sq_nonneg _) (h2SectionEnergy_nonneg _ _)

theorem spectralCoreChartEnergy_integral (F : UpperHalfPlane → ℂ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    (∫ z : UpperHalfPlane in {z | (z.re,z.im) ∈ S}, ‖F z‖^2+h2SectionEnergy F z) =
      ∫ p in S, spectralCoreChartEnergy F p/p.2^2 := by
  simpa only [spectralCoreChartEnergy_at_upper] using
    upperHalfPlane_setIntegral_coordinates (spectralCoreChartEnergy F) hS hpositive

theorem spectralCoreChartEnergy_integrable (F : UpperHalfPlane → ℂ)
    {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hpositive : S ⊆ {p : ℝ × ℝ | 0 < p.2}) :
    IntegrableOn (fun z : UpperHalfPlane => ‖F z‖^2+h2SectionEnergy F z)
      {z | (z.re,z.im) ∈ S} ↔
      IntegrableOn (fun p => spectralCoreChartEnergy F p/p.2^2) S := by
  simpa only [spectralCoreChartEnergy_at_upper] using
    upperHalfPlane_integrableOn_coordinates (spectralCoreChartEnergy F) hS hpositive

end
end ArtinMatthews
