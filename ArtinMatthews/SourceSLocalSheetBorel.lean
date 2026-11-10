module

public import ArtinMatthews.SourceSLocalSheetCoordinates
public import ArtinMatthews.SLocalNormOneHaar
public import Mathlib.MeasureTheory.Group.Circle
public import ArtinMatthews.SourceSLocalSheetTopology
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
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Borel and local compactness API for the genuine sheet product.
The finite products of local Borel spaces agree with the product topology. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open Topology MeasureTheory
open scoped NumberField ArtinMatthews.SourcePhysical
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

theorem sourceSheetFillOne_isClosedEmbedding :
    IsClosedEmbedding (sourceSheetFill S v (1 : v.Completionˣ)) := by
  let f := sourceSheetFill S v (1 : v.Completionˣ)
  have hf : Continuous f := continuous_sourceSheetFill S v continuous_const continuous_id
  have hi : Function.LeftInverse (sourceSheetOther S v) f := sourceSheetOther_fill S v 1
  have hR : Set.range f = {x : SWholeUnits K S | x.1 v = 1} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact sourceSheetFill_chosen S v 1 y
    · intro hx
      have hv : x.1 v = 1 := hx
      refine ⟨sourceSheetOther S v x, ?_⟩
      change sourceSheetFill S v 1 (sourceSheetOther S v x) = x
      rw [← hv]
      exact sourceSheetFill_reconstruct S v x
  refine ⟨hi.isEmbedding (continuous_sourceSheetOther S v) hf, ?_⟩
  rw [hR]
  exact isClosed_eq ((continuous_apply v).comp continuous_fst) continuous_const

theorem sourceSheetOtherUnits_polish : PolishSpace (SNormOneOtherUnits S v) := by
  let : PolishSpace (SWholeUnits K S) := sWholeUnits_polish K S
  exact (sourceSheetFillOne_isClosedEmbedding S v).polishSpace

theorem sourceSheetOtherUnits_locallyCompact : LocallyCompactSpace (SNormOneOtherUnits S v) := by
  let : LocallyCompactSpace (SWholeUnits K S) := sWholeUnits_locallyCompact K S
  exact (sourceSheetFillOne_isClosedEmbedding S v).locallyCompactSpace

private theorem units_secondCountable (F : Type*) [NormedField F] [SecondCountableTopology F] :
    SecondCountableTopology Fˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F)).isEmbedding.secondCountableTopology

omit [NumberField K] in
private theorem infiniteUnits_secondCountable (w : InfinitePlace K) :
    SecondCountableTopology w.Completionˣ := by
  let : SecondCountableTopology w.Completion := by
    rcases w.isReal_or_isComplex with h | h
    · exact (isometryEquivRealOfIsReal h).toHomeomorph.isEmbedding.secondCountableTopology
    · exact (isometryEquivComplexOfIsComplex h).toHomeomorph.isEmbedding.secondCountableTopology
  exact units_secondCountable _

theorem sourceSheetOtherUnits_product_borel
    [∀ w : {w : InfinitePlace K // w ≠ v}, MeasurableSpace w.val.Completionˣ]
    [∀ w : {w : InfinitePlace K // w ≠ v}, BorelSpace w.val.Completionˣ]
    [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ] :
    BorelSpace (SNormOneOtherUnits S v) := by
  let (w : {w : InfinitePlace K // w ≠ v}) : SecondCountableTopology w.val.Completionˣ :=
    infiniteUnits_secondCountable w.val
  let (p : S) : SecondCountableTopology (p.val.adicCompletion K)ˣ := units_secondCountable _
  infer_instance

variable {v}
variable (hv : IsComplex v)

def sourceSNormOneSheetMeasurableEquiv
    [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)] :
    SNormOne K S ≃ᵐ Circle × SNormOneOtherUnits S v :=
  (sourceSNormOneSheetContinuousMulEquiv hv S).toHomeomorph.toMeasurableEquiv

@[simp] theorem sourceSNormOneSheetMeasurableEquiv_apply
    [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)]
    (x : SNormOne K S) :
    sourceSNormOneSheetMeasurableEquiv S hv x = sourceSNormOneToSheet hv S x := rfl

@[simp] theorem sourceSNormOneSheetMeasurableEquiv_symm_apply
    [MeasurableSpace (SNormOneOtherUnits S v)] [BorelSpace (SNormOneOtherUnits S v)]
    (y : Circle × SNormOneOtherUnits S v) :
    (sourceSNormOneSheetMeasurableEquiv S hv).symm y = sourceSNormOneFromSheet hv S y := rfl

def sourceSNormOneSheetProductMeasurableEquiv
    [∀ w : {w : InfinitePlace K // w ≠ v}, MeasurableSpace w.val.Completionˣ]
    [∀ w : {w : InfinitePlace K // w ≠ v}, BorelSpace w.val.Completionˣ]
    [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
    [∀ p : S, BorelSpace (p.val.adicCompletion K)ˣ] :
    SNormOne K S ≃ᵐ Circle × SNormOneOtherUnits S v := by
  let : BorelSpace (SNormOneOtherUnits S v) := sourceSheetOtherUnits_product_borel S v
  exact sourceSNormOneSheetMeasurableEquiv S hv

end
end ArtinMatthews.SourcePhysical
