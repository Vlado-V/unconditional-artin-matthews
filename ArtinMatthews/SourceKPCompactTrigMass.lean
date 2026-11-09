module

public import ArtinMatthews.SourceKPCompactTrigCutoff
public import ArtinMatthews.SourceKPCompactHeightMass
public import ArtinMatthews.SourceKPCompactCoreMassNorm


set_option backward.privateInPublic true
@[expose] public section

/-! The exact height-localized mass and cutoff error for the two-piece partition. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "S" => (fun R : ℝ => Set.ofPred (fun y : Y => sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R))

theorem sourceKPCompactExhaustionC2_tsupport_sublevel (n : ℕ) :
    tsupport (sourceKPCompactExhaustionC2 K hζ n).val ⊆ (S) (Real.exp ((n : ℝ)+2)) := by
  apply closure_minimal _ (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ _).isClosed
  intro y hy
  by_contra hn
  change ¬sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ Real.exp ((n : ℝ)+2) at hn
  apply hy
  rw [sourceKPCompactExhaustionC2_apply,
    sourceKPAutomorphicExhaustionCutoff_eq_zero K hζ n y (lt_of_not_ge hn).le,Complex.ofReal_zero]

theorem sourceKPCompactExhaustionTrigMass_partition (n : ℕ) (f : T) (y : Y) :
    ‖(sourceKPCompactExhaustionCos K hζ n f).val y‖^2 +
      ‖(sourceKPCompactExhaustionSin K hζ n f).val y‖^2 = ‖f.val y‖^2 := by
  rw [sourceKPCompactExhaustionCos_apply,sourceKPCompactExhaustionSin_apply]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [← mul_add,Real.cos_sq_add_sin_sq,mul_one]

theorem sourceKPCompactExhaustionCos_mass_le (n : ℕ) (f : T) :
    (∫ y, ‖(sourceKPCompactExhaustionCos K hζ n f).val y‖^2 ∂μ) ≤
      ∫ y in (S) (Real.exp ((n : ℝ)+2)), ‖f.val y‖^2 ∂μ := by
  let R := Real.exp ((n : ℝ)+2)
  let A := sourceKPCompactExhaustionCos K hζ n f
  let N : Y → ℝ := fun y => ‖f.val y‖^2
  have hS := (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R).measurableSet
  rw [← integral_indicator hS]
  apply integral_mono (sourceKPCompactCore_norm_sq_integrable K hζ A)
    ((sourceKPCompactCore_norm_sq_integrable K hζ f).indicator hS)
  intro y
  change ‖A.val y‖^2 ≤ ((S) R).indicator N y
  by_cases hy : y ∈ (S) R
  · rw [Set.indicator_of_mem hy]
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [sourceKPCompactExhaustionCos_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  · rw [Set.indicator_of_notMem hy]
    change ¬sourceKPAutomorphicCompactOrbitHeight K hζ y ≤ R at hy
    have hη : sourceKPAutomorphicExhaustionCutoff K hζ n y = 0 :=
      sourceKPAutomorphicExhaustionCutoff_eq_zero K hζ n y (lt_of_not_ge hy).le
    rw [sourceKPCompactExhaustionCos_zero K hζ n f y hη,norm_zero]
    norm_num

theorem sourceKPCompactExhaustion_energyMass_integrable (n : ℕ) (f : T) :
    Integrable (fun y => ‖f.val y‖^2 *
      sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y) μ := by
  let : IsFiniteMeasureOnCompacts μ := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  exact ((f.prop.1.norm.pow 2).mul (sourceKPCompactCoreEnergy_continuous K hζ _)).integrable_of_hasCompactSupport
    (sourceKPCompactCoreEnergy_hasCompactSupport K hζ (sourceKPCompactExhaustionC2 K hζ n)).mul_left

theorem sourceKPCompactExhaustion_energyMass_le (n : ℕ) (f : T) (C : ℝ)
    (hC : ∀ y : Y, sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y ≤ C) :
    (∫ y, ‖f.val y‖^2 * sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y ∂μ) ≤
      C * ∫ y in (S) (Real.exp ((n : ℝ)+2)), ‖f.val y‖^2 ∂μ := by
  let R := Real.exp ((n : ℝ)+2)
  let η := sourceKPCompactExhaustionC2 K hζ n
  let N : Y → ℝ := fun y => ‖f.val y‖^2
  have hS := (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R).measurableSet
  rw [← integral_indicator hS,← integral_const_mul]
  apply integral_mono (sourceKPCompactExhaustion_energyMass_integrable K hζ n f)
    (((sourceKPCompactCore_norm_sq_integrable K hζ f).indicator hS).const_mul C)
  intro y
  change N y * sourceKPCompactCoreEnergy K hζ η y ≤ C * ((S) R).indicator N y
  by_cases hy : y ∈ (S) R
  · rw [Set.indicator_of_mem hy,mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC y) (sq_nonneg _)
  · rw [Set.indicator_of_notMem hy,sourceKPCompactCoreEnergy_zero_outside K hζ η
      (fun h => hy (sourceKPCompactExhaustionC2_tsupport_sublevel K hζ n h)),mul_zero,mul_zero]

theorem sourceKPCompactH1LocalizedMass_core_norm_sq_value (R : ℝ) (f : T) :
    ‖sourceKPCompactH1LocalizedMass K hζ R (sourceKPCompactH1Core K hζ ⟨f⟩)‖^2 =
      ∫ y in (S) R, ‖f.val y‖^2 ∂μ := by
  rw [sourceKPCompactH1LocalizedMass_norm_sq,sourceKPCompactH1Mass_core]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (sourceKPCompactCoreMass_coe K hζ f)] with y hy
  change ‖sourceKPCompactCoreMass K hζ 2 f y‖^2 = ‖f.val y‖^2
  rw [hy]

end
end ArtinMatthews
