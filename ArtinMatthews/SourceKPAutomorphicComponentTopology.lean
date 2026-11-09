module

public import ArtinMatthews.SourceKPAutomorphicComponentMeasure
public import ArtinMatthews.SourceKPArchComponentBorel


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

abbrev SourceKPAutomorphicComponentUnion :=
  Σ i : SourceKPFiniteOrbit K hζ,
    SourceKPArchComponentQuotient K hζ (sourceKPFiniteOrbitRepresentative K hζ i)

def sourceKPAutomorphicComponentUnionMap (p : SourceKPAutomorphicComponentUnion K hζ) :
    SourceKPAutomorphicLevel K hζ :=
  sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ p.1) p.2

theorem sourceKPAutomorphicComponentUnionMap_injective :
    Function.Injective (sourceKPAutomorphicComponentUnionMap K hζ) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ h
  have hij := congrArg (sourceKPAutomorphicFiniteOrbit K hζ) h
  simp only [sourceKPAutomorphicComponentUnionMap,
    sourceKPAutomorphicFiniteOrbit_embedding,sourceKPFiniteOrbitRepresentative_spec] at hij
  subst j
  have he := (sourceKPArchComponentEmbedding K hζ (sourceKPFiniteOrbitRepresentative K hζ i)).injective h
  exact congrArg (Sigma.mk i) he

theorem sourceKPAutomorphicComponentUnionMap_surjective :
    Function.Surjective (sourceKPAutomorphicComponentUnionMap K hζ) := by
  intro x
  let i := sourceKPAutomorphicFiniteOrbit K hζ x
  have hx : x ∈ Set.range (sourceKPArchComponentPoint K hζ (sourceKPFiniteOrbitRepresentative K hζ i)) := by
    rw [sourceKPArchComponent_range]
    change sourceKPAutomorphicFiniteOrbit K hζ x = sourceKPFiniteOrbitMk K hζ
      (sourceKPFiniteOrbitRepresentative K hζ i)
    rw [sourceKPFiniteOrbitRepresentative_spec]
  obtain ⟨a,ha⟩ := hx
  exact ⟨⟨i,Quotient.mk _ a⟩,ha⟩

theorem sourceKPAutomorphicComponentUnionMap_continuous :
    Continuous (sourceKPAutomorphicComponentUnionMap K hζ) :=
  continuous_sigma fun i => sourceKPArchComponentEmbedding_continuous K hζ _

theorem sourceKPAutomorphicComponentUnionMap_isOpenMap :
    IsOpenMap (sourceKPAutomorphicComponentUnionMap K hζ) :=
  isOpenMap_sigma.mpr fun i => (sourceKPArchComponentEmbedding_isOpenEmbedding K hζ _).isOpenMap

def sourceKPAutomorphicComponentHomeomorph :
    SourceKPAutomorphicComponentUnion K hζ ≃ₜ SourceKPAutomorphicLevel K hζ :=
  (Equiv.ofBijective (sourceKPAutomorphicComponentUnionMap K hζ)
    ⟨sourceKPAutomorphicComponentUnionMap_injective K hζ,
      sourceKPAutomorphicComponentUnionMap_surjective K hζ⟩).toHomeomorphOfContinuousOpen
        (sourceKPAutomorphicComponentUnionMap_continuous K hζ)
        (sourceKPAutomorphicComponentUnionMap_isOpenMap K hζ)

instance sourceKPAutomorphicLevel_t2 : T2Space (SourceKPAutomorphicLevel K hζ) :=
  (sourceKPAutomorphicComponentHomeomorph K hζ).symm.isEmbedding.t2Space

instance sourceKPAutomorphicLevel_secondCountable : SecondCountableTopology (SourceKPAutomorphicLevel K hζ) :=
  (sourceKPAutomorphicComponentHomeomorph K hζ).symm.isEmbedding.secondCountableTopology

end
end ArtinMatthews
