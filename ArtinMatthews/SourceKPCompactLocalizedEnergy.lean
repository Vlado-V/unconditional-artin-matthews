module

public import ArtinMatthews.SourceKPCompactChartPlateau
public import ArtinMatthews.SourceKPCompactChartIntegrals


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine local Dirichlet test controls energy on its quotient plateau. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

theorem sourceKPCompactCoreLocalized_energy_controls
    (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : SourceKPFiniteChartTests K hζ b p) (W : Set Y) (hW : IsOpen W)
    (hsub : W ⊆ Set.range (sourceKPFiniteChartProjection K hζ b p))
    (hη : ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p,
      sourceKPCompactCoordinateProjection K hζ b x ∈ W → η.val.val =ᶠ[𝓝 x] 1) :
    (∫ y in W, sourceKPCompactCoreEnergy K hζ f y ∂μ) ≤
      ‖h1TestGradient (sourceKPCompactCoreLocalized K hζ f b p η).val‖ ^ 2 := by
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  let R := Set.range (sourceKPFiniteChartProjection K hζ b p)
  let n : ℝ := Nat.card (SourceKPFiniteChartStabilizer K hζ b p)
  let q := sourceKPCompactCoordinateProjection K hζ b
  let E := sourceKPCompactCoreEnergy K hζ f
  let J := W.indicator E
  let φ := (sourceKPCompactCoreLocalized K hζ f b p η).val
  have hJ : Measurable J :=
    (sourceKPCompactCoreEnergy_continuous K hζ f).measurable.indicator hW.measurableSet
  have hJI : Integrable J μ :=
    (sourceKPCompactCoreEnergy_integrable K hζ f).indicator hW.measurableSet
  have hJq : IntegrableOn (J ∘ q) U ν :=
    sourceKPFiniteChart_integrable_pullback K hζ b p J hJ hJI
  have hφI := productGradientEnergy_integrable φ.prop.1 φ.prop.2.1 φ.prop.2.2
  have he (x : ProductSpace (InfinitePlace K)) : 0 ≤ productGradientEnergy φ.val x := by
    change 0 ≤ productGradientEnergy (φ : ProductSpace (InfinitePlace K) → ℂ) x
    rw [← h1GradientAt_norm_sq φ x]
    exact sq_nonneg _
  have hpoint : (J ∘ q) ≤ᵐ[(ν).restrict U] productGradientEnergy φ.val := by
    filter_upwards [ae_restrict_mem (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet,
      sourceKPCompactChartEnergy_ae K hζ f b p] with x hx heq
    change W.indicator E (q x) ≤ productGradientEnergy φ.val x
    by_cases h : q x ∈ W
    · rw [Set.indicator_of_mem h]
      have hh := sourceKPCompactCoreLocalized_gradient_eq K hζ f b p η x (hη x hx h)
      change productGradientEnergy φ.val x = sourceKPCompactCoreEnergyLift K hζ f b x at hh
      rw [hh]
      exact le_of_eq heq.symm
    · rw [Set.indicator_of_notMem h]
      exact he x
  have hc : (∫ x in U, (J ∘ q) x ∂ν) = n * ∫ y in W, E y ∂μ := by
    have h := sourceKPFiniteChart_integral K hζ b p J hJ
    change (∫ x in U, (J ∘ q) x ∂ν) = n * ∫ y in R, J y ∂μ at h
    rw [h]
    dsimp only [J]
    rw [setIntegral_indicator hW.measurableSet,Set.inter_eq_right.mpr hsub]
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ (Nat.card (SourceKPFiniteChartStabilizer K hζ b p) : ℝ)
    have h : 1 ≤ Nat.card (SourceKPFiniteChartStabilizer K hζ b p) := Nat.card_pos
    exact_mod_cast h
  have he0 : 0 ≤ ∫ y in W, E y ∂μ := integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f)
  calc
    _ ≤ n * ∫ y in W, E y ∂μ := le_mul_of_one_le_left he0 hn
    _ = ∫ x in U, (J ∘ q) x ∂ν := hc.symm
    _ ≤ ∫ x in U, productGradientEnergy φ.val x ∂ν := integral_mono_ae hJq hφI.integrableOn hpoint
    _ ≤ ∫ x, productGradientEnergy φ.val x ∂ν :=
      setIntegral_le_integral hφI (Eventually.of_forall he)
    _ = _ := (h1TestGradient_norm_sq φ).symm

end
end ArtinMatthews
