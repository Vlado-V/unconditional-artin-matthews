module

public import ArtinMatthews.SourceKPCuspPrincipalQuotient
public import ArtinMatthews.SourceAdelicTraceHaar
public import ArtinMatthews.UnitTorusWeakGradient
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

/-! The principal cusp quotient carries the probability Haar measure induced by
    the actual trace-normalized additive adelic fundamental domain. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free MeasureTheory Topology Set
open scoped NumberField AdeleRing Classical ENNReal Pointwise
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local instance : MeasurableSpace 𝔸[K] := borel 𝔸[K]
local instance : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance : MeasurableSpace Q := borel Q
local instance : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspTraceHaar : Measure Q :=
  Measure.map (QuotientAddGroup.mk : 𝔸[K] → Q)
    ((sourceKPAdelicTraceProduct K).restrict (sourceKPAdelicFundamentalDomain K))

lemma sourceKPCuspTraceHaar_apply (S : Set Q) (hS : MeasurableSet S) :
    sourceKPCuspTraceHaar K d S = sourceKPAdelicTraceProduct K
      ((QuotientAddGroup.mk : 𝔸[K] → Q) ⁻¹' S ∩ sourceKPAdelicFundamentalDomain K) := by
  rw [sourceKPCuspTraceHaar, Measure.map_apply QuotientAddGroup.continuous_mk.measurable hS,
    Measure.restrict_apply (QuotientAddGroup.continuous_mk.measurable hS)]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
include hζ

lemma sourceKPCuspTraceHaar_probability : IsProbabilityMeasure (sourceKPCuspTraceHaar K d) := by
  constructor
  rw [sourceKPCuspTraceHaar_apply K d univ MeasurableSet.univ, preimage_univ, univ_inter]
  exact sourceKPAdelicTraceProduct_fundamentalDomain_of_primitiveRoot K hζ

lemma sourceKPCuspTraceHaar_addInvariant : (sourceKPCuspTraceHaar K d).IsAddLeftInvariant := by
  let ν := sourceKPAdelicTraceProduct K
  let D := sourceKPAdelicFundamentalDomain K
  let q : 𝔸[K] →+ Q := QuotientAddGroup.mk' (sourceKPCuspPrincipalPeriods K d)
  let : ν.IsAddHaarMeasure := by
    dsimp only [ν]
    rw [sourceKPAdelicTraceProduct_eq_standard_of_primitiveRoot K hζ]
    infer_instance
  have hq : Continuous q := QuotientAddGroup.continuous_mk
  have hD : IsAddFundamentalDomain (sourceKPAdelicRationals K) D ν :=
    sourceKPAdelicFundamentalDomain_isFundamental K ν
  constructor
  intro z
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
  ext S hS
  rw [Measure.map_apply (measurable_const_add _) hS,
    sourceKPCuspTraceHaar_apply K d _ ((measurable_const_add _) hS),
    sourceKPCuspTraceHaar_apply K d S hS]
  change ν (q ⁻¹' ((q a + ·) ⁻¹' S) ∩ D) = ν (q ⁻¹' S ∩ D)
  have he : q ⁻¹' ((q a + ·) ⁻¹' S) = (a + ·) ⁻¹' (q ⁻¹' S) := by
    ext x
    simp only [mem_preimage, map_add]
  rw [he]
  have ht : ν ((a + ·) ⁻¹' (q ⁻¹' S) ∩ D) =
      ν (q ⁻¹' S ∩ (-a + ·) ⁻¹' D) := by
    trans ν ((a + ·) ⁻¹' (q ⁻¹' S ∩ (-a + ·) ⁻¹' D))
    · congr 1
      ext x
      simp only [mem_inter_iff, mem_preimage, neg_add_cancel_left]
    · rw [measure_preimage_add]
  rw [ht]
  have htranslate : IsAddFundamentalDomain (sourceKPAdelicRationals K) ((-a + ·) ⁻¹' D) ν := by
    have hset : ((-a + ·) ⁻¹' D) = a +ᵥ D := by
      ext x
      change (-a + x ∈ D) ↔ ∃ y, y ∈ D ∧ a + y = x
      constructor
      · intro hx
        exact ⟨-a + x, hx, by abel⟩
      · rintro ⟨y, hy, rfl⟩
        simpa only [neg_add_cancel_left] using hy
    rw [hset]
    exact hD.vadd_of_comm a
  exact htranslate.measure_set_eq hD (hq.measurable hS) (by
    intro r
    ext x
    change q ((r : 𝔸[K]) + x) ∈ S ↔ q x ∈ S
    rw [map_add]
    have hr : q (r : 𝔸[K]) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_sup_left r.property)
    rw [hr, zero_add])

variable (hd : d ≠ 0)
include hd

lemma sourceKPCuspTraceHaar_isAddHaarMeasure :
    (sourceKPCuspTraceHaar K d).IsAddHaarMeasure := by
  let := sourceKPCuspPrincipalQuotient_compact K d hd
  let := sourceKPCuspPrincipalQuotient_t2 K d hd
  let := sourceKPCuspTraceHaar_probability K d hζ
  let := sourceKPCuspTraceHaar_addInvariant K d hζ
  exact MeasureTheory.Measure.isAddHaarMeasure_of_isCompact_nonempty_interior
    (sourceKPCuspTraceHaar K d) univ isCompact_univ (by simp) (by simp) (by simp)

lemma sourceKPCuspPrincipalTorus_measurePreserving :
    MeasurePreserving (sourceKPCuspPrincipalTorusHomeomorph K d hd)
      (sourceKPCuspTraceHaar K d) (unitTorusHaar I) := by
  let := sourceKPCuspTraceHaar_probability K d hζ
  let := sourceKPCuspTraceHaar_isAddHaarMeasure K d hζ hd
  apply (sourceKPCuspPrincipalTorusHomeomorph K d hd).toAddEquiv.toAddMonoidHom.measurePreserving
  · exact (sourceKPCuspPrincipalTorusHomeomorph K d hd).continuous
  · exact (sourceKPCuspPrincipalTorusHomeomorph K d hd).surjective
  · simp

lemma sourceKPCuspPrincipalTorus_symm_measurePreserving :
    MeasurePreserving (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm
      (unitTorusHaar I) (sourceKPCuspTraceHaar K d) :=
  MeasurePreserving.symm
    (sourceKPCuspPrincipalTorusHomeomorph K d hd).toHomeomorph.toMeasurableEquiv
    (sourceKPCuspPrincipalTorus_measurePreserving K d hζ hd)

end
end ArtinMatthews
