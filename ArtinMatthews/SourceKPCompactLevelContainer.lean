module

public import ArtinMatthews.SourceKPFiniteOrbit
public import ArtinMatthews.SourceKPFiniteIntegralIndex
public import ArtinMatthews.SourceKPHeightLocalContinuity


set_option backward.privateInPublic true
@[expose] public section

/-! Compact containers for all actual cover lifts of a compact matrix set.
The finite-level quotient carries its actual archimedean-times-discrete topology;
no topology is imposed on the full finite central cover. -/

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicArchProjective (g : GL (Fin 2) 𝔸[K]) : PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).1)

theorem sourceKPAdelicArchProjective_continuous : Continuous (sourceKPAdelicArchProjective K) := by
  have harch : Continuous (fun g : GL (Fin 2) 𝔸[K] => (sourceKPGL2ProductEquiv K g).1) := by
    change Continuous (GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing K) 𝔸ᶠ[K]))
    exact continuous_fst.generalLinearGroup_map
  exact QuotientGroup.continuous_mk.comp harch

def sourceKPCompactFiniteFibers (S : Set (GL (Fin 2) 𝔸[K])) :
    Set (SourceKPFiniteLevelFiber K hζ) :=
  (QuotientGroup.mk : SourceKPFiniteAdeleProjective K hζ → SourceKPFiniteLevelFiber K hζ) ''
    ((sourceKPFiniteAdeleProjectiveProjection K hζ) ⁻¹'
      (ProjGenLinGroup.mk '' ((fun g => (sourceKPGL2ProductEquiv K g).2) '' S)))

theorem sourceKPCompactFiniteFibers_finite (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    (sourceKPCompactFiniteFibers K hζ S).Finite :=
  sourceKPFiniteCover_compact_image_finite K hζ _
    (hS.image (sourceKPAdelicFiniteMatrix_continuous K))

def sourceKPCompactLevelContainer (S : Set (GL (Fin 2) 𝔸[K])) :
    Set (SourceKPFiniteLevelSpace K hζ) :=
  (sourceKPAdelicArchProjective K '' S) ×ˢ sourceKPCompactFiniteFibers K hζ S

theorem sourceKPCompactLevelContainer_isCompact
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    IsCompact (sourceKPCompactLevelContainer K hζ S) :=
  (hS.image (sourceKPAdelicArchProjective_continuous K)).prod
    (sourceKPCompactFiniteFibers_finite K hζ S hS).isCompact

theorem sourceKPCompactLevelContainer_mem
    (S : Set (GL (Fin 2) 𝔸[K])) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : g ∈ S)
    (hq : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    sourceKPFiniteLevelMk K hζ q ∈ sourceKPCompactLevelContainer K hζ S := by
  have he := congrArg (sourceKPAdelicProjectiveProductEquiv K) hq
  rw [sourceKPAdelicProjectiveProjection_product] at he
  change (q.1, sourceKPFiniteAdeleProjectiveProjection K hζ q.2) =
    (ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).1),
      ProjGenLinGroup.mk ((sourceKPGL2ProductEquiv K g).2)) at he
  refine ⟨⟨g,hg,(congrArg Prod.fst he).symm⟩,?_⟩
  refine ⟨q.2,?_,rfl⟩
  exact ⟨(sourceKPGL2ProductEquiv K g).2,⟨g,hg,rfl⟩,(congrArg Prod.snd he).symm⟩

def sourceKPCompactAutomorphicContainer (S : Set (GL (Fin 2) 𝔸[K])) :
    Set (SourceKPAutomorphicLevel K hζ) :=
  (Quotient.mk (MulAction.orbitRel (PGL(2, K)) (SourceKPFiniteLevelSpace K hζ))) ''
    sourceKPCompactLevelContainer K hζ S

theorem sourceKPCompactAutomorphicContainer_isCompact
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    IsCompact (sourceKPCompactAutomorphicContainer K hζ S) :=
  (sourceKPCompactLevelContainer_isCompact K hζ S hS).image continuous_quot_mk

theorem sourceKPCompactAutomorphicContainer_mem
    (S : Set (GL (Fin 2) 𝔸[K])) (q : SourceKPAdelicProjective K hζ)
    (g : GL (Fin 2) 𝔸[K]) (hg : g ∈ S)
    (hq : sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g) :
    sourceKPAutomorphicLevelMk K hζ q ∈ sourceKPCompactAutomorphicContainer K hζ S :=
  ⟨sourceKPFiniteLevelMk K hζ q,sourceKPCompactLevelContainer_mem K hζ S q g hg hq,rfl⟩

theorem sourceKPCompactAutomorphicContainer_finite_components
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    Set.Finite ((sourceKPAutomorphicFiniteOrbit K hζ) ''
      sourceKPCompactAutomorphicContainer K hζ S) :=
  ((sourceKPCompactAutomorphicContainer_isCompact K hζ S hS).image
    (sourceKPAutomorphicFiniteOrbit_continuous K hζ)).finite_of_discrete

end
end ArtinMatthews
