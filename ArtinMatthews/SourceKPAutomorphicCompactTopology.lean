module

public import ArtinMatthews.SourceKPArchDoubleQuotient
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPAutomorphicComponentTopology
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
public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPFiniteLevelSpace_locallyCompact :
    LocallyCompactSpace (SourceKPFiniteLevelSpace K hζ) := by
  change LocallyCompactSpace (PGL(2, InfiniteAdeleRing K) × SourceKPFiniteLevelFiber K hζ)
  infer_instance

instance sourceKPAutomorphicLevel_locallyCompact :
    LocallyCompactSpace (SourceKPAutomorphicLevel K hζ) := by
  change LocallyCompactSpace
    (Quotient (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ)))
  exact MulAction.isOpenQuotientMap_quotientMk.locallyCompactSpace

/-- The actual compact right action is proper on the full automorphic quotient. -/
instance sourceKPAutomorphicLevel_compactRight_proper :
    ProperSMul (SourceKPArchCompactRightGroup K hζ) (SourceKPAutomorphicLevel K hζ) := by
  constructor
  apply isProperMap_iff_isCompact_preimage.mpr
  have hc : Continuous (fun p : SourceKPArchCompactRightGroup K hζ ×
      SourceKPAutomorphicLevel K hζ => (p.1 • p.2, p.2)) :=
    continuous_smul.prodMk continuous_snd
  refine ⟨hc, ?_⟩
  intro C hC
  apply ((isCompact_univ (X := SourceKPArchCompactRightGroup K hζ)).prod
    (hC.image continuous_snd)).of_isClosed_subset (hC.isClosed.preimage hc)
  intro p hp
  exact ⟨Set.mem_univ _, ⟨(p.1 • p.2, p.2), hp, rfl⟩⟩

instance sourceKPAutomorphicCompactLevel_t2 :
    T2Space (SourceKPAutomorphicCompactLevel K hζ) := by
  change T2Space (Quotient (MulAction.orbitRel (SourceKPArchCompactRightGroup K hζ)
    (SourceKPAutomorphicLevel K hζ)))
  infer_instance

instance sourceKPAutomorphicCompactLevel_secondCountable :
    SecondCountableTopology (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).secondCountableTopology

instance sourceKPAutomorphicCompactLevel_locallyCompact :
    LocallyCompactSpace (SourceKPAutomorphicCompactLevel K hζ) :=
  (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).locallyCompactSpace

/-- Quotienting by the compact right group is a proper map. -/
theorem sourceKPAutomorphicCompactMk_isProperMap :
    IsProperMap (sourceKPAutomorphicCompactMk K hζ) := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨(sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous, ?_, ?_⟩
  · exact MulAction.isClosedMap_quotient
  · intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      have hfiber : (sourceKPAutomorphicCompactMk K hζ) ⁻¹'
          {sourceKPAutomorphicCompactMk K hζ x} =
          Set.range (fun g : SourceKPArchCompactRightGroup K hζ => g • x) := by
        ext y
        constructor
        · intro hy
          change sourceKPAutomorphicCompactMk K hζ y =
            sourceKPAutomorphicCompactMk K hζ x at hy
          exact MulAction.mem_orbit_iff.mp (Quotient.exact hy)
        · rintro ⟨g, rfl⟩
          apply Quotient.sound
          exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
      change IsCompact ((sourceKPAutomorphicCompactMk K hζ) ⁻¹'
        {sourceKPAutomorphicCompactMk K hζ x})
      rw [hfiber]
      exact isCompact_range (show Continuous (fun g : SourceKPArchCompactRightGroup K hζ =>
        g • x) from continuous_id.smul continuous_const)

theorem sourceKPAutomorphicCompactMk_isCompact_preimage
    {C : Set (SourceKPAutomorphicCompactLevel K hζ)} (hC : IsCompact C) :
    IsCompact ((sourceKPAutomorphicCompactMk K hζ) ⁻¹' C) :=
  (sourceKPAutomorphicCompactMk_isProperMap K hζ).isCompact_preimage hC

end
end ArtinMatthews
