module

public import ArtinMatthews.SourceKPAutomorphicComponentTopology
public import ArtinMatthews.SourceKPArchDoubleQuotient
public import Mathlib.Topology.Algebra.ProperAction.CompactlyGenerated
public import Mathlib.Topology.Algebra.Group.Pointwise


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
