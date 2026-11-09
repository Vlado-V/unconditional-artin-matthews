module

public import ArtinMatthews.SourceKPCubicCoreAction
public import ArtinMatthews.SourceKPCompactCoreMass


set_option backward.privateInPublic true
@[expose] public section

/-! The literal core average agrees with the actual Haar L² projector. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff BigOperators ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] sourceKPCompactCubicCenter_fintype

theorem sourceKPCubicCoreMass_pullback (n : ℕ∞ω) (z : rootsOfUnity 3 K)
    (f : sourceKPCompactCore K hζ n) :
    sourceKPCompactCoreMass K hζ n (sourceKPCubicCorePullback K hζ n z f) =
      sourceKPCompactCubicL2Representation K hζ (sourceKPArchHaar K hζ) z
        (sourceKPCompactCoreMass K hζ n f) := by
  apply Lp.ext
  have hm := sourceKPCompactCoreMass_coe K hζ (sourceKPCubicCorePullback K hζ n z f)
  have hu := sourceKPCompactCubicL2Representation_ae K hζ (sourceKPArchHaar K hζ) z
    (sourceKPCompactCoreMass K hζ n f)
  have hf := (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹
    (sourceKPArchHaar K hζ)).quasiMeasurePreserving.ae_eq_comp
      (sourceKPCompactCoreMass_coe K hζ f)
  filter_upwards [hm, hu, hf] with x hm hu hf
  calc
    _ = f.val (z⁻¹ • x) := hm
    _ = sourceKPCompactCoreMass K hζ n f (z⁻¹ • x) := hf.symm
    _ = _ := hu.symm

theorem sourceKPCubicCoreMass_projector (n : ℕ∞ω) (f : sourceKPCompactCore K hζ n) :
    sourceKPCompactCoreMass K hζ n (sourceKPCubicCoreProjector K hζ n f) =
      sourceKPGenuineAutomorphicL2Projector K hζ (sourceKPCompactCoreMass K hζ n f) := by
  rw [sourceKPGenuineAutomorphicL2Projector, sourceKPCompactGenuineL2Projector_apply_three]
  simp only [sourceKPCubicCoreProjector, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, sourceKPCubicCoreMass_pullback]

theorem sourceKPGenuineAutomorphicL2Projector_preserves_core (n : ℕ∞ω)
    {f : SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ)}
    (hf : f ∈ (sourceKPCompactCoreMass K hζ n).range) :
    sourceKPGenuineAutomorphicL2Projector K hζ f ∈ (sourceKPCompactCoreMass K hζ n).range := by
  obtain ⟨g, rfl⟩ := hf
  exact ⟨sourceKPCubicCoreProjector K hζ n g, sourceKPCubicCoreMass_projector K hζ n g⟩

theorem sourceKPCubicCoreMass_projector_mem_genuine (n : ℕ∞ω) (f : sourceKPCompactCore K hζ n) :
    sourceKPCompactCoreMass K hζ n (sourceKPCubicCoreProjector K hζ n f) ∈
      sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ) := by
  rw [sourceKPCubicCoreMass_projector, sourceKPGenuineAutomorphicL2Projector,
    ← sourceKPCompactGenuineL2Projector_range]
  exact ⟨sourceKPCompactCoreMass K hζ n f, rfl⟩

end
end ArtinMatthews
