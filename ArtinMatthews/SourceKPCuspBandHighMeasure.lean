module

public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPHighCuspMeasure
public import ArtinMatthews.SourceKPCompactHeight


set_option backward.privateInPublic true
@[expose] public section

/-! The band pairing transported to the actual full high quotient. -/

namespace ArtinMatthews
open NumberField MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "X" => SourceKPAutomorphicLevel K hζ
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "π" => sourceKPAutomorphicCompactMk K hζ
local notation "μX" => sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPAutomorphicBandIntegral_integrable_high (G : Y → ℂ) (hG : Integrable G μY) (T : ℝ) :
    Integrable (fun x : SourceKPHighCuspAutomorphic K hζ T => G (π x.val))
      (sourceKPHighCuspMeasure K hζ T) := by
  have hπ := sourceKPAutomorphicCompactMk_measurePreserving K hζ (sourceKPArchHaar K hζ)
  have hX : Integrable (G ∘ π) μX := hπ.integrable_comp_of_integrable hG
  have hX' : Integrable (G ∘ π) (Measure.map Subtype.val (sourceKPHighCuspMeasure K hζ T)) := by
    rw [sourceKPHighCuspMeasure_map_val]
    exact hX.integrableOn
  have hEmb : MeasurableEmbedding (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → X) :=
    MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  exact hEmb.integrable_map_iff.mp hX'

theorem sourceKPAutomorphicBandIntegral_eq_high (G : Y → ℂ) (hG : Integrable G μY) (T : ℝ)
    (hzero : ∀ y : Y, sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ T → G y = 0) :
    (∫ y : Y, G y ∂μY) =
      ∫ x : SourceKPHighCuspAutomorphic K hζ T, G (π x.val) ∂sourceKPHighCuspMeasure K hζ T := by
  let S : Set X := {x | T < sourceKPAutomorphicOrbitHeight K hζ x}
  have hS : MeasurableSet S := (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  calc
    _ = ∫ x : X, G (π x) ∂μX :=
      integral_map (sourceKPAutomorphicCompactMk_measurable K hζ).aemeasurable hG.aestronglyMeasurable
    _ = ∫ x in S, G (π x) ∂μX := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hHx : sourceKPAutomorphicOrbitHeight K hζ x ≤ T := le_of_not_gt hx
      exact hzero (π x) hHx
    _ = _ := (integral_subtype_comap hS (fun x : X => G (π x))).symm

end
end ArtinMatthews
