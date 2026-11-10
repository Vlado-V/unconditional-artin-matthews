module

public import ArtinMatthews.SLocalNormOneGroup
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Local compactness and countability for the genuine finite product
of completion unit groups and its closed norm-one subgroup. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain Topology
open scoped NumberField Classical
noncomputable section

private theorem normedField_units_polish (F : Type*) [NormedField F] [PolishSpace F] :
    PolishSpace Fˣ := by
  have h : IsOpenEmbedding (Units.val : Fˣ → F) := IsOpenUnits.isOpenEmbedding_unitsVal
  let : PolishSpace (Set.range (Units.val : Fˣ → F)) := h.isOpen_range.polishSpace
  exact h.isEmbedding.toHomeomorph.isClosedEmbedding.polishSpace

private theorem normedField_units_locallyCompact (F : Type*) [NormedField F] [LocallyCompactSpace F] :
    LocallyCompactSpace Fˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F)).locallyCompactSpace

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

omit [NumberField K] in
private theorem infiniteCompletion_polish (w : InfinitePlace K) : PolishSpace w.Completion := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isClosedEmbedding.polishSpace
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isClosedEmbedding.polishSpace

omit [NumberField K] in
private theorem infiniteCompletion_locallyCompact (w : InfinitePlace K) : LocallyCompactSpace w.Completion := by
  rcases w.isReal_or_isComplex with hw | hw
  · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.isOpenEmbedding.locallyCompactSpace
  · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.isOpenEmbedding.locallyCompactSpace

theorem sWholeUnits_polish : PolishSpace (SWholeUnits K S) := by
  let (w : InfinitePlace K) : PolishSpace w.Completionˣ := by
    let : PolishSpace w.Completion := infiniteCompletion_polish K w
    exact normedField_units_polish _
  let (v : S) : PolishSpace (v.val.adicCompletion K)ˣ := normedField_units_polish _
  infer_instance

theorem sWholeUnits_locallyCompact : LocallyCompactSpace (SWholeUnits K S) := by
  let (w : InfinitePlace K) : LocallyCompactSpace w.Completionˣ := by
    let : LocallyCompactSpace w.Completion := infiniteCompletion_locallyCompact K w
    exact normedField_units_locallyCompact _
  let (v : S) : LocallyCompactSpace (v.val.adicCompletion K)ˣ := normedField_units_locallyCompact _
  infer_instance

theorem sNormOne_polish : PolishSpace (SNormOne K S) := by
  let : PolishSpace (SWholeUnits K S) := sWholeUnits_polish K S
  exact (sNormOneSubgroup_isClosed K S).polishSpace

theorem sNormOne_locallyCompact : LocallyCompactSpace (SNormOne K S) := by
  let : LocallyCompactSpace (SWholeUnits K S) := sWholeUnits_locallyCompact K S
  exact (sNormOneSubgroup_isClosed K S).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sNormOneSixthQuotient_secondCountable : SecondCountableTopology (SNormOneSixthQuotient K S) := by
  let : PolishSpace (SNormOne K S) := sNormOne_polish K S
  exact QuotientGroup.isOpenQuotientMap_mk.secondCountableTopology

end
end ArtinMatthews.SourcePhysical
