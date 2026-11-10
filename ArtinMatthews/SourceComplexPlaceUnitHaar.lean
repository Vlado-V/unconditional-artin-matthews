module

public import ArtinMatthews.SourceComplexUnitHaar
public import ArtinMatthews.SourceSLocalRadialSection
public import Mathlib.Analysis.CStarAlgebra.Classes
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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField ENNReal
noncomputable section

variable {K : Type} [Field K] {v : InfinitePlace K} (hv : IsComplex v)

def sourceComplexPlaceUnitsEquiv : v.Completionˣ ≃ₜ* ℂˣ :=
  Units.mapContinuousMulEquiv
    { toMulEquiv := (ringEquivComplexOfIsComplex hv).toMulEquiv
      continuous_toFun := (isometryEquivComplexOfIsComplex hv).continuous
      continuous_invFun := (isometryEquivComplexOfIsComplex hv).symm.continuous }

theorem sourceComplexPlaceUnitsEquiv_val (u : v.Completionˣ) :
    (sourceComplexPlaceUnitsEquiv hv u : ℂ) = ringEquivComplexOfIsComplex hv (u : v.Completion) := rfl

theorem sourceComplexPlaceUnitsEquiv_radial (t : ℝ) :
    sourceComplexPlaceUnitsEquiv hv (sourceComplexPlaceRadialUnit hv t) = sourceComplexRadialUnit t := by
  apply Units.ext
  rw [sourceComplexPlaceUnitsEquiv_val]
  change ringEquivComplexOfIsComplex hv ((ringEquivComplexOfIsComplex hv).symm (Real.exp (t / 2) : ℂ)) =
    (Real.exp (t / 2) : ℂ)
  exact (ringEquivComplexOfIsComplex hv).apply_symm_apply _

variable [MeasurableSpace v.Completion] [BorelSpace v.Completion]

theorem sourceComplexPlaceUnits_borel : BorelSpace v.Completionˣ := by
  constructor
  change (inferInstance : MeasurableSpace v.Completion).comap Units.val = borel v.Completionˣ
  rw [BorelSpace.measurable_eq (α := v.Completion), ← borel_comap]
  congr 1
  exact Units.isEmbedding_val₀.isInducing.eq_induced.symm

/-- The normalized complex-place Haar on the literal number field completion units. -/
def sourceComplexPlaceUnitHaar : Measure v.Completionˣ :=
  Measure.map (sourceComplexPlaceUnitsEquiv hv).symm sourceComplexUnitHaar

theorem sourceComplexPlaceUnitHaar_isHaar : (sourceComplexPlaceUnitHaar hv).IsHaarMeasure := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  have : sourceComplexUnitHaar.IsHaarMeasure := sourceComplexUnitHaar_isHaar
  exact (sourceComplexPlaceUnitsEquiv hv).symm.isHaarMeasure_map sourceComplexUnitHaar

theorem sourceComplexPlaceUnitHaar_map_complex :
    Measure.map (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ))
      (sourceComplexPlaceUnitHaar hv) =
      sourceComplexTraceMeasure.withDensity (fun z : ℂ => ENNReal.ofReal ((‖z‖ ^ 2)⁻¹)) := by
  have : BorelSpace v.Completionˣ := sourceComplexPlaceUnits_borel (v := v)
  have h₁ : Measurable (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ)) :=
    Units.continuous_val.measurable.comp (sourceComplexPlaceUnitsEquiv hv).continuous.measurable
  have h₂ : Measurable ((sourceComplexPlaceUnitsEquiv hv).symm : ℂˣ → v.Completionˣ) :=
    (sourceComplexPlaceUnitsEquiv hv).symm.continuous.measurable
  rw [sourceComplexPlaceUnitHaar, Measure.map_map h₁ h₂]
  have he : (fun u : v.Completionˣ => (sourceComplexPlaceUnitsEquiv hv u : ℂ)) ∘
      (sourceComplexPlaceUnitsEquiv hv).symm = (Units.val : ℂˣ → ℂ) := by
    funext z
    simp only [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
  rw [he, sourceComplexUnitHaar_map_val]

end
end ArtinMatthews.SourcePhysical
