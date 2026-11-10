module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.FieldCoordinates
public import OAI.RepresentationTheory.Weil.Local.ArchimedeanTestSpace
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! # Complex Field Haar -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFieldHaar.Construction

noncomputable section

/-! The complex Lebesgue Haar factor and the transported reference compact set. -/

open _root_.MeasureTheory Set _root_.TopologicalSpace
open scoped NNReal

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k]

def fieldComplexHaarFactor (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) : ℝ≥0 :=
  FieldCoordinates.Construction.fieldReferenceHaarFactor e he he' * ArchimedeanTestSpace.Construction.complexReferenceHaarFactor

theorem fieldComplexHaarFactor_pos (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    0 < fieldComplexHaarFactor e he he' :=
  mul_pos (FieldCoordinates.Construction.fieldReferenceHaarFactor_pos e he he') ArchimedeanTestSpace.Construction.complexReferenceHaarFactor_pos

theorem fieldComplexHaar_map (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).map e = fieldComplexHaarFactor e he he' • volume := by
  rw [FieldCoordinates.Construction.fieldReferenceHaar_map e he he',
    Measure.isAddLeftInvariant_eq_smul_of_regular (Measure.addHaar : Measure ℂ) volume, smul_smul]
  rfl

theorem fieldComplexHaar_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) (f : k → E) :
    (∫ x, f x ∂Measure.addHaar) =
      (fieldComplexHaarFactor e he he' : ℝ) • ∫ y : ℂ, f (e.symm y) := by
  have hi := integral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y))
  change (∫ y, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldComplexHaar_map e he he', integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def] using hi.symm

def complexFieldReferenceCompact (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm) :
    PositiveCompacts ℂ :=
  (FunctionsMetaplectic.Construction.referenceCompact k).map e he (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.isOpenMap

omit [MeasurableSpace k] [BorelSpace k] in
theorem complexFieldReferenceCompact_volume_pos (e : k ≃+* ℂ) (he : Continuous e)
    (he' : Continuous e.symm) :
    0 < volume.real (complexFieldReferenceCompact e he he' : Set ℂ) := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior volume
      (complexFieldReferenceCompact e he he').interior_nonempty).ne'
  · exact (complexFieldReferenceCompact e he he').isCompact.measure_ne_top

theorem complexFieldReferenceCompact_measure (e : k ≃+* ℂ) (he : Continuous e)
    (he' : Continuous e.symm) :
    (Measure.addHaar : Measure k).real (FunctionsMetaplectic.Construction.referenceCompact k : Set k) =
      (fieldComplexHaarFactor e he he' : ℝ) *
        volume.real (complexFieldReferenceCompact e he he' : Set ℂ) := by
  have hm := congrArg (fun μ : Measure ℂ => μ.real (complexFieldReferenceCompact e he he' : Set ℂ))
    (fieldComplexHaar_map e he he')
  rw [map_measureReal_apply he.measurable (complexFieldReferenceCompact e he he').isCompact.measurableSet,
    measureReal_nnreal_smul_apply] at hm
  have hpre : e ⁻¹' (complexFieldReferenceCompact e he he' : Set ℂ) =
      (FunctionsMetaplectic.Construction.referenceCompact k : Set k) := e.injective.preimage_image _
  rwa [hpre] at hm

theorem fieldComplexHaar_setIntegral (e : k ≃+* ℂ) (he : Continuous e) (he' : Continuous e.symm)
    (f : k → ℂ) (s : Set ℂ) :
    (∫ x in e ⁻¹' s, f x ∂Measure.addHaar) =
      (fieldComplexHaarFactor e he he' : ℂ) * ∫ y in s, f (e.symm y) := by
  have hi := setIntegral_map_equiv (μ := (Measure.addHaar : Measure k))
    (FieldCoordinates.Construction.fieldAddHomeomorph e he he').toHomeomorph.toMeasurableEquiv (fun y => f (e.symm y)) s
  change (∫ y in s, f (e.symm y) ∂(Measure.addHaar : Measure k).map e) =
    ∫ x in e ⁻¹' s, f (e.symm (e x)) ∂Measure.addHaar at hi
  rw [fieldComplexHaar_map e he he', Measure.restrict_smul, integral_smul_nnreal_measure] at hi
  simpa only [RingEquiv.symm_apply_apply, NNReal.smul_def, Complex.real_smul] using hi.symm

end

end OAI.RepresentationTheory.Weil.Local.ComplexFieldHaar.Construction
