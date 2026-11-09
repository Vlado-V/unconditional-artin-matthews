module

public import ArtinMatthews.SourceKPHeightBandReduction
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing Pointwise
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPHeightBandMatrices_isCompact (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPHeightBandMatrices K hζ v₀ a b) :=
  (sourceKPAdelicBorelBand_isCompact K hζ v₀ a b).mul
    (SourceKPAdelicBaseCompactMatrix_isCompact K hζ)

theorem sourceKPHeightBand_automorphic_container_isCompact
    (v₀ : InfinitePlace K) (a b : ℝ) :
    IsCompact (sourceKPCompactAutomorphicContainer K hζ
      (sourceKPHeightBandMatrices K hζ v₀ a b)) :=
  sourceKPCompactAutomorphicContainer_isCompact K hζ _
    (sourceKPHeightBandMatrices_isCompact K hζ v₀ a b)

theorem sourceKPHeightBand_compact_container (v₀ : InfinitePlace K) (a b : ℝ) :
    ∃ C : Set (SourceKPAutomorphicLevel K hζ), IsCompact C ∧
      ∀ (q : SourceKPAdelicProjective K hζ) (g : GL (Fin 2) 𝔸[K]),
        sourceKPAdelicProjectiveProjection K hζ q = ProjGenLinGroup.mk g →
        Real.log (sourceKPAdelicHeight K hζ g) ∈ Set.Icc a b →
          sourceKPAutomorphicLevelMk K hζ q ∈ C := by
  refine ⟨sourceKPCompactAutomorphicContainer K hζ
    (sourceKPHeightBandMatrices K hζ v₀ a b),
      sourceKPHeightBand_automorphic_container_isCompact K hζ v₀ a b,?_⟩
  exact sourceKPHeightBand_cover_reduction K hζ v₀ a b

theorem sourceKPHeightBand_finite_components (v₀ : InfinitePlace K) (a b : ℝ) :
    Set.Finite ((sourceKPAutomorphicFiniteOrbit K hζ) ''
      sourceKPCompactAutomorphicContainer K hζ (sourceKPHeightBandMatrices K hζ v₀ a b)) :=
  sourceKPCompactAutomorphicContainer_finite_components K hζ _
    (sourceKPHeightBandMatrices_isCompact K hζ v₀ a b)

end
end ArtinMatthews
