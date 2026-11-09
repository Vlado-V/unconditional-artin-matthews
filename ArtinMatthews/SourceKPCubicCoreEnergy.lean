module

public import ArtinMatthews.SourceKPCubicCoreAction
public import ArtinMatthews.SourceKPCompactCoreEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual center pullback preserves the global native Dirichlet integral. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCoreEnergy_covariant (z : rootsOfUnity 3 K)
    (f : sourceKPCompactC2Core K hζ) (y : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f) y =
      sourceKPCompactCoreEnergy K hζ f (z⁻¹ • y) := by
  obtain ⟨b, p, rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  rw [sourceKPCubicCenter_upperToCompact, sourceKPCompactCoreEnergy_chart,
    sourceKPCompactCoreEnergy_chart, sourceKPCubicCorePullback_energy]

theorem sourceKPCubicCoreEnergy_integral (z : rootsOfUnity 3 K)
    (f : sourceKPCompactC2Core K hζ) :
    (∫ y, sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f) y
      ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) =
      ∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  simp_rw [sourceKPCubicCoreEnergy_covariant]
  exact (sourceKPAutomorphicCompactMeasure_center_preserving K hζ z⁻¹
    (sourceKPArchHaar K hζ)).integral_comp
      (sourceKPCubicCenterCompactHomeomorph K hζ z⁻¹).measurableEmbedding
      (sourceKPCompactCoreEnergy K hζ f)

end
end ArtinMatthews
