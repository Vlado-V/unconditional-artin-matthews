module

public import ArtinMatthews.SourceKPCompactCoreLocalization
public import ArtinMatthews.SourceKPCompactChartIntegrals
public import ArtinMatthews.SourceHyperbolicH1LocalMulBounds


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCoreLocalized_mass_bound
    (f : sourceKPCompactC2Core K hζ) (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) (M : ℝ)
    (hη : ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p, ‖η.val.val x‖ ≤ M) :
    ‖h1TestMass (sourceKPCompactCoreLocalized K hζ f b p η).val‖ ^ 2 ≤
      (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) * M ^ 2 *
        ‖sourceKPCompactCoreMass K hζ 2 f‖ ^ 2 := by
  have hlocal := h1LocalTestMul_mass_norm_sq_le
    (sourceKPFiniteChartCoordinateDomain K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
    η (sourceKPCompactChartPullback K hζ f.val b)
    ((f.prop.2.2 b).mono (sourceKPFiniteChartCoordinateDomain_upper K hζ b p))
    M hη (sourceKPCompactChart_mass_integrable K hζ f b p)
  change ‖h1TestMass (sourceKPCompactCoreLocalized K hζ f b p η).val‖ ^ 2 ≤ _ at hlocal
  rw [sourceKPCompactChart_mass_integral] at hlocal
  have hmass := setIntegral_le_integral (sourceKPCompactCore_norm_sq_integrable K hζ f)
    (Filter.Eventually.of_forall (fun y => sq_nonneg ‖f.val y‖))
    (s := Set.range (sourceKPFiniteChartProjection K hζ b p))
  refine hlocal.trans ?_
  calc
    _ ≤ M ^ 2 * ((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
        ∫ y, ‖f.val y‖ ^ 2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity)) (sq_nonneg M)
    _ = _ := by rw [← sourceKPCompactCoreMass_norm_sq]; ring

theorem sourceKPCompactCoreLocalized_gradient_bound
    (f : sourceKPCompactC2Core K hζ) (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) (M B : ℝ)
    (hη : ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p, ‖η.val.val x‖ ≤ M)
    (hEη : ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p,
      productGradientEnergy η.val.val x ≤ B) :
    ‖h1TestGradient (sourceKPCompactCoreLocalized K hζ f b p η).val‖ ^ 2 ≤
      2 * (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
        (M ^ 2 * (∫ y, sourceKPCompactCoreEnergy K hζ f y
            ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) +
          B * ‖sourceKPCompactCoreMass K hζ 2 f‖ ^ 2) := by
  have hB : 0 ≤ B := by
    have hzero : 0 ≤ productGradientEnergy η.val.val (sourceKPArchUpperEuclideanMap K p) := by
      unfold productGradientEnergy
      positivity
    exact hzero.trans (hEη _ (sourceKPFiniteChartCoordinateDomain_mem K hζ b p))
  have hlocal := h1LocalTestMul_gradient_norm_sq_le
    (sourceKPFiniteChartCoordinateDomain K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p)
    η (sourceKPCompactChartPullback K hζ f.val b)
    ((f.prop.2.2 b).mono (sourceKPFiniteChartCoordinateDomain_upper K hζ b p))
    M B hη hEη (sourceKPCompactChart_mass_integrable K hζ f b p)
    (sourceKPCompactChart_energy_integrable K hζ f b p)
  change ‖h1TestGradient (sourceKPCompactCoreLocalized K hζ f b p η).val‖ ^ 2 ≤ _ at hlocal
  rw [sourceKPCompactChart_mass_integral, sourceKPCompactChart_energy_integral] at hlocal
  have hmass := setIntegral_le_integral (sourceKPCompactCore_norm_sq_integrable K hζ f)
    (Filter.Eventually.of_forall (fun y => sq_nonneg ‖f.val y‖))
    (s := Set.range (sourceKPFiniteChartProjection K hζ b p))
  have henergy := setIntegral_le_integral (sourceKPCompactCoreEnergy_integrable K hζ f)
    (Filter.Eventually.of_forall (sourceKPCompactCoreEnergy_nonneg K hζ f))
    (s := Set.range (sourceKPFiniteChartProjection K hζ b p))
  refine hlocal.trans ?_
  calc
    _ ≤ 2 * (M ^ 2 * ((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
          ∫ y, sourceKPCompactCoreEnergy K hζ f y
            ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) +
        B * ((Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ) *
          ∫ y, ‖f.val y‖ ^ 2
            ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      exact add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy (by positivity)) (sq_nonneg M))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmass (by positivity)) hB)
    _ = _ := by rw [← sourceKPCompactCoreMass_norm_sq]; ring

end
end ArtinMatthews
