module

public import ArtinMatthews.SourceKPCompactSetMassPairing
public import ArtinMatthews.SourceKPCompactEnergyRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! Compact native tests use their actual image in the compact automorphic quotient. -/
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

theorem sourceKPCompactCoordinateProjection_continuousOn :
    ContinuousOn q (productUpper (InfinitePlace K)) :=
  (sourceKPUpperToCompact_continuous K hζ b).comp_continuousOn
    (sourceKPArchEuclideanUpperMap_continuousOn K)

def sourceKPCompactNativeTestImage (S : Set X) : Set Y := q '' S

theorem sourceKPCompactNativeTestImage_isCompact (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) :
    IsCompact (sourceKPCompactNativeTestImage K hζ b S) :=
  hS.image_of_continuousOn ((sourceKPCompactCoordinateProjection_continuousOn K hζ b).mono hSu)

theorem sourceKPCompactNativeTestImage_mem (S : Set X) {x : X} (hx : x ∈ S) :
    q x ∈ sourceKPCompactNativeTestImage K hζ b S := ⟨x, hx, rfl⟩

theorem sourceKPCompactSetMassPairing_cutoff (S : Set X) (hS : IsCompact S)
    (hSu : S ⊆ productUpper (InfinitePlace K)) (φ : X → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ x ∈ S, ‖φ x‖ ≤ C)
    (Q : Set Y) (hQ : MeasurableSet Q) (himage : q '' S ⊆ Q) (g : Lp ℂ 2 μ) :
    sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC (measurableL2Cutoff μ Q hQ g) =
      sourceKPCompactSetMassPairing K hζ b S hS hSu φ hφ C hC g := by
  rw [sourceKPCompactSetMassPairing_apply_of_ae K hζ b S hS hSu φ hφ C hC
      (measurableL2Cutoff μ Q hQ g) (measurableL2Cutoff_coe μ Q hQ g),
    sourceKPCompactSetMassPairing_apply K hζ b S hS hSu φ hφ C hC g]
  apply setIntegral_congr_fun hS.measurableSet
  intro x hx
  dsimp only
  rw [Set.indicator_of_mem (himage ⟨x, hx, rfl⟩)]

end
end ArtinMatthews
