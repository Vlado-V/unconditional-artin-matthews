module

public import ArtinMatthews.SourceKPFiniteStabilizerCompact
public import ArtinMatthews.SourceAdelicRationalTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic discreteness of each actual finite-level archimedean
component, obtained from additive adelic rational discreteness. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPArchProjective_locallyCompact :
    LocallyCompactSpace (PGL(2, InfiniteAdeleRing K)) := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  change LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K) ⧸
    Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))
  infer_instance

instance sourceKPArchProjective_t2 : T2Space (PGL(2, InfiniteAdeleRing K)) :=
  T2Space.of_injective_continuous sourceProjectiveConjugationCoordinates_injective
    sourceProjectiveConjugationCoordinates_continuous

def sourceConjugationAdeleJoin
    (a : (SourceConjugationIndex → InfiniteAdeleRing K) ×
      (SourceConjugationIndex → 𝔸ᶠ[K])) : SourceConjugationIndex → 𝔸[K] :=
  fun p => (a.1 p, a.2 p)

theorem sourceConjugationAdeleJoin_continuous :
    Continuous (sourceConjugationAdeleJoin K) := by
  apply continuous_pi
  intro p
  exact ((continuous_apply p).comp continuous_fst).prodMk
    ((continuous_apply p).comp continuous_snd)

theorem sourceKPRationalFiniteStabilizer_compact_finite
    (b : SourceKPFiniteLevelFiber K hζ) (C : Set (PGL(2, InfiniteAdeleRing K)))
    (hC : IsCompact C) :
    Set.Finite {γ : PGL(2, K) | γ ∈ sourceKPRationalFiniteStabilizer K hζ b ∧
      sourceKPRationalArchMap K hζ γ ∈ C} := by
  obtain ⟨D, hD, hrep⟩ := sourceKPRationalFiniteStabilizer_compact_representatives K hζ b
  let E := sourceConjugationAdeleJoin K ''
    ((sourceProjectiveConjugationCoordinates '' C) ×ˢ
      (sourceGLConjugationCoordinates '' D))
  have hE : IsCompact E :=
    ((hC.image sourceProjectiveConjugationCoordinates_continuous).prod
      (hD.image sourceGLConjugationCoordinates_continuous)).image
        (sourceConjugationAdeleJoin_continuous K)
  have hf := OAI.RepresentationTheory.Weil.AdelicSplitting.RationalDiscreteness.Construction.finite_rational_positions_preimage_compact K E hE
  apply Set.Finite.of_finite_image (f := sourceProjectiveConjugationCoordinates) _
    (Set.injOn_of_injective sourceProjectiveConjugationCoordinates_injective)
  apply hf.subset
  rintro _ ⟨γ, ⟨hγ, hγC⟩, rfl⟩
  obtain ⟨g, hg, hproj⟩ := hrep γ hγ
  refine ⟨(sourceProjectiveConjugationCoordinates (sourceKPRationalArchMap K hζ γ),
    sourceGLConjugationCoordinates g), ⟨Set.mem_image_of_mem _ hγC,
      Set.mem_image_of_mem _ hg⟩, ?_⟩
  funext p
  apply Prod.ext
  · exact congrFun (sourceProjectiveConjugationCoordinates_map
      (algebraMap K (InfiniteAdeleRing K)) γ) p
  · change sourceGLConjugationCoordinates g p =
      algebraMap K 𝔸ᶠ[K] (sourceProjectiveConjugationCoordinates γ p)
    rw [← sourceProjectiveConjugationCoordinates_mk, ← hproj,
      sourceProjectiveConjugationCoordinates_map]

theorem sourceKPArchComponentSubgroup_compact_finite
    (b : SourceKPFiniteLevelFiber K hζ) (C : Set (PGL(2, InfiniteAdeleRing K)))
    (hC : IsCompact C) :
    Set.Finite {g : sourceKPArchComponentSubgroup K hζ b |
      (g : PGL(2, InfiniteAdeleRing K)) ∈ C} := by
  have hf := (sourceKPRationalFiniteStabilizer_compact_finite K hζ b C hC).image
    (sourceKPRationalArchMap K hζ)
  apply Set.Finite.of_finite_image (f := Subtype.val) _
    (Set.injOn_of_injective Subtype.val_injective)
  apply hf.subset
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨γ, hγ, he⟩ := g.property
  exact ⟨γ, ⟨hγ, he.symm ▸ hg⟩, he⟩

instance sourceKPArchComponentSubgroup_discrete (b : SourceKPFiniteLevelFiber K hζ) :
    DiscreteTopology (sourceKPArchComponentSubgroup K hζ b) := by
  apply continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact
  rw [tendsto_cofinite_cocompact_iff]
  intro C hC
  exact sourceKPArchComponentSubgroup_compact_finite K hζ b C hC

theorem sourceKPArchComponentSubgroup_isClosed (b : SourceKPFiniteLevelFiber K hζ) :
    IsClosed (sourceKPArchComponentSubgroup K hζ b : Set (PGL(2, InfiniteAdeleRing K))) :=
  Subgroup.isClosed_of_discreteTopology

end
end ArtinMatthews
