module

public import ArtinMatthews.SourceKPCompactSetMassLift


set_option backward.privateInPublic true
@[expose] public section

/-! A bounded measurable test on a compact positive set defines an exact scalar pairing. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter Set
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)
local notation "q" => sourceKPCompactCoordinateProjection K hζ b

theorem sourceKPCompactSetMassTest_memLp (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) : MemLp (S.indicator φ) 2 ν := by
  let : IsFiniteMeasure ((ν).restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using productVolume_compact_lt_top hS hSu⟩
  refine (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).mpr
    (MemLp.of_bound hφ.aestronglyMeasurable C ?_)
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC x hx

def sourceKPCompactSetMassPairing (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  (innerSL ℂ ((sourceKPCompactSetMassTest_memLp K S hS hSu φ hφ C hC).toLp (S.indicator φ))).comp
    (sourceKPCompactSetMassLift K hζ b S hS hSu)

private theorem sourceKPCompactSetMassPairing_integrand_ae (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) (g : Lp ℂ 2 μ)
    {u : Y → ℂ} (hu : (g : Y → ℂ) =ᵐ[μ] u) :
    (fun x => inner ℂ
      (((sourceKPCompactSetMassTest_memLp K S hS hSu φ hφ C hC).toLp (S.indicator φ)) x)
      (sourceKPCompactSetMassLift K hζ b S hS hSu g x)) =ᵐ[ν]
      S.indicator (fun x => star (φ x) * u (q x)) := by
  filter_upwards [(sourceKPCompactSetMassTest_memLp K S hS hSu φ hφ C hC).coeFn_toLp,
    sourceKPCompactSetMassLift_coe_of_ae K hζ b S hS hSu g hu] with x hφx hux
  change inner ℂ _ _ = _
  rw [hφx, hux]
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx, Function.comp_apply]
    exact RCLike.inner_apply' _ _
  · simp only [Set.indicator_of_notMem hx, inner_zero_left]

theorem sourceKPCompactSetMassPairing_apply_of_ae (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) (g : Lp ℂ 2 μ)
    {u : Y → ℂ} (hu : (g : Y → ℂ) =ᵐ[μ] u) :
    sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC g =
      ∫ x in S, star (φ x) * u (q x) ∂ν := by
  rw [sourceKPCompactSetMassPairing, ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
    ← integral_indicator hS.measurableSet]
  exact integral_congr_ae (sourceKPCompactSetMassPairing_integrand_ae K hζ b S hS hSu φ hφ C hC g hu)

theorem sourceKPCompactSetMassPairing_apply (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) (g : Lp ℂ 2 μ) :
    sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC g =
      ∫ x in S, star (φ x) * g (q x) ∂ν :=
  sourceKPCompactSetMassPairing_apply_of_ae K hζ b S hS hSu φ hφ C hC g Filter.EventuallyEq.rfl

theorem sourceKPCompactSetMassPairing_integrableOn_of_ae (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C) (g : Lp ℂ 2 μ)
    {u : Y → ℂ} (hu : (g : Y → ℂ) =ᵐ[μ] u) :
    IntegrableOn (fun x => star (φ x) * u (q x)) S ν := by
  rw [← integrable_indicator_iff hS.measurableSet]
  exact (L2.integrable_inner (𝕜 := ℂ) ((sourceKPCompactSetMassTest_memLp K S hS hSu φ hφ C hC).toLp
    (S.indicator φ)) (sourceKPCompactSetMassLift K hζ b S hS hSu g)).congr
    (sourceKPCompactSetMassPairing_integrand_ae K hζ b S hS hSu φ hφ C hC g hu)

end
end ArtinMatthews
