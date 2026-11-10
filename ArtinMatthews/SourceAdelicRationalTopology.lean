module

public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.AdeleRing
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient
public import OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational additive subgroup of the adele ring is discrete,
closed, and cocompact. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Filter
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Topology RestrictedProduct
noncomputable section
variable (K : Type) [Field K] [NumberField K]

instance sourceKPInfiniteAdeleT2 : T2Space (InfiniteAdeleRing K) := by
  change T2Space ((v : InfinitePlace K) → v.Completion)
  infer_instance

instance sourceKPFiniteAdeleT2 : T2Space 𝔸ᶠ[K] := by
  change T2Space (Πʳ P : HeightOneSpectrum (𝓞 K), [P.adicCompletion K, P.adicCompletionIntegers K])
  infer_instance

instance sourceKPFiniteAdeleWeaklyLocallyCompact : WeaklyLocallyCompactSpace 𝔸ᶠ[K] := by
  let : Fact (∀ P : HeightOneSpectrum (𝓞 K), IsOpen (P.adicCompletionIntegers K : Set (P.adicCompletion K))) :=
    ⟨fun P => Valued.isOpen_valuationSubring (P.adicCompletion K)⟩
  change WeaklyLocallyCompactSpace (Πʳ P : HeightOneSpectrum (𝓞 K), [P.adicCompletion K, P.adicCompletionIntegers K])
  infer_instance

instance sourceKPAdelicNontrivial : Nontrivial 𝔸[K] := by
  change Nontrivial (InfiniteAdeleRing K × 𝔸ᶠ[K])
  infer_instance

instance sourceKPAdelicT2 : T2Space 𝔸[K] := by
  change T2Space (InfiniteAdeleRing K × 𝔸ᶠ[K])
  infer_instance

instance sourceKPAdelicWeaklyLocallyCompact : WeaklyLocallyCompactSpace 𝔸[K] := by
  change WeaklyLocallyCompactSpace (InfiniteAdeleRing K × 𝔸ᶠ[K])
  infer_instance

def sourceKPAdelicRationals : AddSubgroup 𝔸[K] :=
  (algebraMap K 𝔸[K]).toAddMonoidHom.range

def sourceKPRationalAdeleEquiv : K ≃+ sourceKPAdelicRationals K :=
  AddEquiv.ofBijective (algebraMap K 𝔸[K]).toAddMonoidHom.rangeRestrict
    ⟨fun _ _ h => (algebraMap K 𝔸[K]).injective (congrArg Subtype.val h),
      (algebraMap K 𝔸[K]).toAddMonoidHom.rangeRestrict_surjective⟩

theorem sourceKPRationalAdeleEquiv_apply (q : K) :
    (sourceKPRationalAdeleEquiv K q : 𝔸[K]) = algebraMap K 𝔸[K] q := rfl

instance sourceKPNumberFieldCountable : Countable K :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

instance sourceKPAdelicRationals_countable : Countable (sourceKPAdelicRationals K) :=
  (sourceKPRationalAdeleEquiv K).symm.injective.countable

theorem sourceKPAdelicRationals_compact_finite (C : Set 𝔸[K]) (hC : IsCompact C) :
    Set.Finite {q : sourceKPAdelicRationals K | (q : 𝔸[K]) ∈ C} := by
  have h := RationalDiscreteness.Construction.finite_rational_preimage_compact K C hC
  have hi := h.image (sourceKPRationalAdeleEquiv K)
  apply hi.subset
  rintro q hq
  obtain ⟨x, rfl⟩ := (sourceKPRationalAdeleEquiv K).surjective q
  exact ⟨x, hq, rfl⟩

instance sourceKPAdelicRationals_discrete : DiscreteTopology (sourceKPAdelicRationals K) := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro C hC
  exact sourceKPAdelicRationals_compact_finite K C hC

theorem sourceKPAdelicRationals_isClosed : IsClosed (sourceKPAdelicRationals K : Set 𝔸[K]) :=
  AddSubgroup.isClosed_of_discreteTopology

abbrev SourceKPAdditiveAdeleQuotient := 𝔸[K] ⧸ sourceKPAdelicRationals K

theorem sourceKPAdelicRational_quotient_zero (q : K) :
    (QuotientAddGroup.mk (algebraMap K 𝔸[K] q) : SourceKPAdditiveAdeleQuotient K) = 0 := by
  exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨q, rfl⟩

instance sourceKPAdditiveAdeleQuotient_compact : CompactSpace (SourceKPAdditiveAdeleQuotient K) := by
  let C := CompactQuotient.Construction.adelicCompactRepresentatives K
  have hC : IsCompact C := CompactQuotient.Construction.isCompact_adelicCompactRepresentatives K
  have hi : IsCompact (QuotientAddGroup.mk '' C : Set (SourceKPAdditiveAdeleQuotient K)) :=
    hC.image QuotientAddGroup.continuous_mk
  have he : (QuotientAddGroup.mk '' C : Set (SourceKPAdditiveAdeleQuotient K)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨q, hq⟩ := CompactQuotient.Construction.rational_translates_cover_adeles K a
    refine ⟨a - algebraMap K 𝔸[K] q, hq, ?_⟩
    change (QuotientAddGroup.mk' (sourceKPAdelicRationals K)) (a - algebraMap K 𝔸[K] q) = _
    rw [map_sub]
    have hzero : (QuotientAddGroup.mk' (sourceKPAdelicRationals K)) (algebraMap K 𝔸[K] q) = 0 :=
      sourceKPAdelicRational_quotient_zero K q
    rw [hzero, sub_zero]
    rfl
  rw [he] at hi
  exact isCompact_univ_iff.mp hi

end
end ArtinMatthews
