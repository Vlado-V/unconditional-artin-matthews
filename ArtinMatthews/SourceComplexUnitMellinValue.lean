module

public import ArtinMatthews.SourceComplexUnitMellin
public import ArtinMatthews.SourceComplexPlaceUnitHaar
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace ArtinMatthews.SourcePhysical
open MeasureTheory Set Filter
open ArtinMatthews.VaryingKummerAnalytic
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped ENNReal NNReal SchwartzMap
noncomputable section

/-- The actual multiplicative Haar Mellin integral equals the normalized trace-density integral. -/
theorem sourceComplexUnitHaar_mellin_eq (g : 𝓢(ℂ, ℂ)) (s : ℂ) :
    (∫ z : ℂˣ, sourceComplexUnitMellinIntegrand g s z ∂sourceComplexUnitHaar) =
      sourceComplexMellin g s := by
  let ρ : ℂ → ℝ≥0 := fun z => (‖z‖₊ ^ 2)⁻¹
  have hρ : Measurable ρ := by
    unfold ρ
    fun_prop
  have hD : (fun z => (ρ z : ℝ≥0∞)) = sourceComplexNormDensity := by
    funext z
    rw [sourceComplexNormDensity, ← ENNReal.ofReal_coe_nnreal]
    congr 1
  have hm := (sourceComplexUnitMellinIntegrand_measurable g s).aestronglyMeasurable
    (μ := Measure.map (Units.val : ℂˣ → ℂ) sourceComplexUnitHaar)
  rw [← integral_map Units.continuous_val.measurable.aemeasurable hm, sourceComplexUnitHaar_map_val]
  change (∫ z : ℂ, sourceComplexUnitMellinIntegrand g s z
      ∂sourceComplexTraceMeasure.withDensity sourceComplexNormDensity) = _
  rw [← hD, integral_withDensity_eq_integral_smul hρ]
  unfold sourceComplexMellin
  apply integral_congr_ae
  filter_upwards [sourceComplexTraceMeasure_ae_ne_zero] with z hz
  have h := sourceComplexNormDensity_smul_integrand g s z hz
  rw [← hD] at h
  exact h

variable {K : Type} [Field K] {v : InfinitePlace K} (hv : IsComplex v)
variable [MeasurableSpace v.Completion] [BorelSpace v.Completion]

theorem sourceComplexPlaceUnitHaar_equiv_measurePreserving :
    MeasurePreserving (sourceComplexPlaceUnitsEquiv hv) (sourceComplexPlaceUnitHaar hv)
      sourceComplexUnitHaar := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  let e := (sourceComplexPlaceUnitsEquiv hv).toHomeomorph.toMeasurableEquiv
  change MeasurePreserving e (sourceComplexPlaceUnitHaar hv) sourceComplexUnitHaar
  exact ⟨e.measurable, e.map_map_symm⟩

theorem sourceComplexPlaceUnitHaar_mellin_eq (g : 𝓢(ℂ, ℂ)) (s : ℂ) :
    (∫ z : v.Completionˣ,
      sourceComplexUnitMellinIntegrand g s (sourceComplexPlaceUnitsEquiv hv z)
        ∂sourceComplexPlaceUnitHaar hv) = sourceComplexMellin g s := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  let e := (sourceComplexPlaceUnitsEquiv hv).toHomeomorph.toMeasurableEquiv
  have he : MeasurePreserving e (sourceComplexPlaceUnitHaar hv) sourceComplexUnitHaar :=
    sourceComplexPlaceUnitHaar_equiv_measurePreserving hv
  exact (he.integral_comp e.measurableEmbedding
    (fun z : ℂˣ => sourceComplexUnitMellinIntegrand g s z)).trans (sourceComplexUnitHaar_mellin_eq g s)

theorem sourceComplexPlaceUnitMellinIntegrand_integrable (g : 𝓢(ℂ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun z : v.Completionˣ =>
      sourceComplexUnitMellinIntegrand g s (sourceComplexPlaceUnitsEquiv hv z))
      (sourceComplexPlaceUnitHaar hv) :=
  (sourceComplexPlaceUnitHaar_equiv_measurePreserving hv).integrable_comp_of_integrable
    (sourceComplexUnitMellinIntegrand_integrable g s hs)

end
end ArtinMatthews.SourcePhysical
