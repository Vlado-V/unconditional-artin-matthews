module

public import ArtinMatthews.SourceKPCubicAverageNorm
public import ArtinMatthews.SourceKPCubicCoreMass
public import ArtinMatthews.SourceKPCubicCoreEnergy
public import ArtinMatthews.SourceKPCompactCoreGradient
public import ArtinMatthews.SourceKPCompactEnergyRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! Energy contraction for the actual compact-core cubic character projector. -/
namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] sourceKPCompactCubicCenter_fintype

theorem sourceKPCubicCoreProjector_gradientAt (f : sourceKPCompactC2Core K hζ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCompactCoreGradientAtLinear K hζ y (sourceKPCubicCoreProjector K hζ 2 f) =
      (3 : ℂ)⁻¹ • ∑ z : rootsOfUnity 3 K, (sourceKPAdelicCentralComplex K hζ z : ℂ) •
        sourceKPCompactCoreGradientAtLinear K hζ y (sourceKPCubicCorePullback K hζ 2 z f) := by
  simp only [sourceKPCubicCoreProjector, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]

theorem sourceKPCubicCoreEnergy_projector_pointwise (f : sourceKPCompactC2Core K hζ)
    (y : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCompactCoreEnergy K hζ (sourceKPCubicCoreProjector K hζ 2 f) y ≤
      (3 : ℝ)⁻¹ * ∑ z : rootsOfUnity 3 K,
        sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f) y := by
  rw [← sourceKPCompactCoreGradientAt_norm_sq K hζ (sourceKPCubicCoreProjector K hζ 2 f) y,
    sourceKPCubicCoreProjector_gradientAt]
  simpa only [sourceKPCompactCoreGradientAt_norm_sq] using
    sourceKPCubicWeightedAverage_norm_sq_le K hζ
      (fun z => sourceKPCompactCoreGradientAtLinear K hζ y (sourceKPCubicCorePullback K hζ 2 z f))

theorem sourceKPCubicCoreEnergy_projector_le (f : sourceKPCompactC2Core K hζ) :
    (∫ y, sourceKPCompactCoreEnergy K hζ (sourceKPCubicCoreProjector K hζ 2 f) y
      ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) ≤
      ∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  let μ := sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
  let shiftedEnergy (z : rootsOfUnity 3 K) : SourceKPAutomorphicCompactLevel K hζ → ℝ :=
    sourceKPCompactCoreEnergy K hζ (sourceKPCubicCorePullback K hζ 2 z f)
  have hs (z : rootsOfUnity 3 K) : Integrable (shiftedEnergy z) μ :=
    sourceKPCompactCoreEnergy_integrable K hζ (sourceKPCubicCorePullback K hζ 2 z f)
  have hsum : Integrable (fun y => ∑ z, shiftedEnergy z y) μ :=
    integrable_finsetSum Finset.univ (fun z _ => hs z)
  have hi (z : rootsOfUnity 3 K) :
      (∫ y, shiftedEnergy z y ∂μ) = ∫ y, sourceKPCompactCoreEnergy K hζ f y ∂μ :=
    sourceKPCubicCoreEnergy_integral K hζ z f
  calc
    _ ≤ ∫ y, (3 : ℝ)⁻¹ * ∑ z, shiftedEnergy z y ∂μ :=
      integral_mono (sourceKPCompactCoreEnergy_integrable K hζ _)
        (hsum.const_mul _) (sourceKPCubicCoreEnergy_projector_pointwise K hζ f)
    _ = (3 : ℝ)⁻¹ * ∑ z, ∫ y, shiftedEnergy z y ∂μ := by
      rw [integral_const_mul, integral_finsetSum Finset.univ (fun z _ => hs z)]
    _ = _ := by
      simp only [hi, Finset.sum_const, Finset.card_univ, sourceKPCubicCenter_card_three K hζ,
        nsmul_eq_mul, Nat.cast_ofNat]
      ring

theorem sourceKPCubicCoreProjector_massEnergy_le (f : sourceKPCompactC2Core K hζ) :
    ‖sourceKPCompactCoreMass K hζ 2 (sourceKPCubicCoreProjector K hζ 2 f)‖ ^ 2 +
      (∫ y, sourceKPCompactCoreEnergy K hζ (sourceKPCubicCoreProjector K hζ 2 f) y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) ≤
    ‖sourceKPCompactCoreMass K hζ 2 f‖ ^ 2 +
      (∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  have hm : ‖sourceKPCompactCoreMass K hζ 2 (sourceKPCubicCoreProjector K hζ 2 f)‖ ≤
      ‖sourceKPCompactCoreMass K hζ 2 f‖ := by
    rw [sourceKPCubicCoreMass_projector]
    calc
      _ ≤ ‖sourceKPGenuineAutomorphicL2Projector K hζ‖ * ‖sourceKPCompactCoreMass K hζ 2 f‖ :=
        (sourceKPGenuineAutomorphicL2Projector K hζ).le_opNorm _
      _ ≤ 1 * ‖sourceKPCompactCoreMass K hζ 2 f‖ :=
        mul_le_mul_of_nonneg_right
          (sourceKPCompactGenuineL2Projector_norm_le K hζ (sourceKPArchHaar K hζ)) (norm_nonneg _)
      _ = _ := one_mul _
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hm 2)
    (sourceKPCubicCoreEnergy_projector_le K hζ f)

end
end ArtinMatthews
