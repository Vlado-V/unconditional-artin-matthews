module

public import ArtinMatthews.SourceKPCompactH1Completion
public import ArtinMatthews.SourceKPCompactCoreLocalizationBounds
public import ArtinMatthews.H1LocalUniformBounds
public import ArtinMatthews.SourceHyperbolicH1LocalEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! Actual chart localization extends continuously to the scalar mass-and-energy completion. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen UniformSpace
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "T" => SourceKPCompactFormCore K hζ
local notation "A" => H1EnergySpace (InfinitePlace K)
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

def sourceKPCompactCoreLocalizationLinear (η : h1LocalTests U) :
    T →ₗ[ℂ] A :=
  h1EnergyCoreLinear.comp ({
    toFun := fun f => (sourceKPCompactCoreLocalized K hζ f.val b p η).val
    map_add' := by
      intro f g
      apply Subtype.ext
      funext x
      change η.val.val x * sourceKPCompactChartPullback K hζ (f.val+g.val).val b x =
        η.val.val x * sourceKPCompactChartPullback K hζ f.val.val b x +
          η.val.val x * sourceKPCompactChartPullback K hζ g.val.val b x
      simp only [Submodule.coe_add,sourceKPCompactChartPullback_add,Pi.add_apply,mul_add]
    map_smul' := by
      intro a f
      change (sourceKPCompactCoreLocalized K hζ (a • f).val b p η).val =
        a • (sourceKPCompactCoreLocalized K hζ f.val b p η).val
      apply Subtype.ext
      funext x
      change η.val.val x * sourceKPCompactChartPullback K hζ (a • f.val).val b x =
        a * (η.val.val x * sourceKPCompactChartPullback K hζ f.val.val b x)
      simp only [Submodule.coe_smul,sourceKPCompactChartPullback_smul,Pi.smul_apply,smul_eq_mul]
      ring
  } : T →ₗ[ℂ] h1Tests (InfinitePlace K) 2)

theorem sourceKPCompactCoreLocalizationLinear_apply (η : h1LocalTests U) (f : T) :
    sourceKPCompactCoreLocalizationLinear K hζ b p η f =
      h1EnergyCore (sourceKPCompactCoreLocalized K hζ f.val b p η).val := rfl

theorem sourceKPCompactCoreLocalization_bounds (η : h1LocalTests U) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ f : T, ‖sourceKPCompactCoreLocalizationLinear K hζ b p η f‖ ≤ C * ‖f‖) ∧
      ∀ f : T, ‖h1EnergyMass (InfinitePlace K) (sourceKPCompactCoreLocalizationLinear K hζ b p η f)‖ ≤
        C * ‖sourceKPCompactFormCoreMassLinear K hζ f‖ := by
  obtain ⟨M,B,hM,hB,hη,hEη⟩ := h1LocalTest_uniform_bounds U η
  let n : ℝ := Nat.card (SourceKPFiniteChartStabilizer K hζ b p)
  let D := n*(3*M^2 + 2*B)
  have hn : 0 ≤ n := by positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have h1 : n*M^2 + 2*n*B ≤ D := by dsimp only [D]; nlinarith [mul_nonneg hn (sq_nonneg M)]
  have h2 : 2*n*M^2 ≤ D := by
    dsimp only [D]
    nlinarith [mul_nonneg hn (sq_nonneg M),mul_nonneg hn hB]
  have h3 : n*M^2 ≤ D := by
    dsimp only [D]
    nlinarith [mul_nonneg hn hB,mul_nonneg hn (sq_nonneg M)]
  refine ⟨Real.sqrt D,Real.sqrt_nonneg _,?_,?_⟩
  · intro f
    let e := ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ
    let m := ‖sourceKPCompactFormCoreMassLinear K hζ f‖ ^ 2
    have hem : 0 ≤ e := integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val)
    have hm : 0 ≤ m := sq_nonneg _
    have hf := sourceKPCompactCoreLocalized_mass_bound K hζ f.val b p η M (fun x _ => hη x)
    have hg := sourceKPCompactCoreLocalized_gradient_bound K hζ f.val b p η M B
      (fun x _ => hη x) (fun x _ => hEη x)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [sourceKPCompactCoreLocalizationLinear_apply,h1Energy_norm_sq,h1EnergyMass_core,h1EnergyGradient_core,
      mul_pow,Real.sq_sqrt hD,sourceKPCompactFormCore_norm_sq]
    calc
      _ ≤ n*M^2*m + 2*n*(M^2*e + B*m) := add_le_add hf hg
      _ = (n*M^2+2*n*B)*m + (2*n*M^2)*e := by ring
      _ ≤ D*m + D*e := add_le_add (mul_le_mul_of_nonneg_right h1 hm) (mul_le_mul_of_nonneg_right h2 hem)
      _ = _ := (mul_add D m e).symm
  · intro f
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [sourceKPCompactCoreLocalizationLinear_apply,h1EnergyMass_core,mul_pow,Real.sq_sqrt hD]
    exact (sourceKPCompactCoreLocalized_mass_bound K hζ f.val b p η M (fun x _ => hη x)).trans
      (mul_le_mul_of_nonneg_right h3 (sq_nonneg _))

def sourceKPCompactCoreLocalization (η : h1LocalTests U) :
    T →L[ℂ] A :=
  (sourceKPCompactCoreLocalizationLinear K hζ b p η).mkContinuous
    (sourceKPCompactCoreLocalization_bounds K hζ b p η).choose
    (sourceKPCompactCoreLocalization_bounds K hζ b p η).choose_spec.2.1

def sourceKPCompactH1Localization (η : h1LocalTests U) :
    SourceKPCompactH1 K hζ →L[ℂ] A :=
  (sourceKPCompactCoreLocalization K hζ b p η).fromCompletion

theorem sourceKPCompactH1Localization_core (η : h1LocalTests U) (f : T) :
    sourceKPCompactH1Localization K hζ b p η (sourceKPCompactH1Core K hζ f) =
      h1EnergyCore (sourceKPCompactCoreLocalized K hζ f.val b p η).val :=
  (sourceKPCompactCoreLocalization K hζ b p η).fromCompletion_apply_coe f

theorem sourceKPCompactH1Localization_zero_of_mass_zero (η : h1LocalTests U)
    (u : SourceKPCompactH1 K hζ) (hu : sourceKPCompactH1Mass K hζ u = 0) :
    sourceKPCompactH1Localization K hζ b p η u = 0 := by
  obtain ⟨C,hC,_,hbound⟩ := sourceKPCompactCoreLocalization_bounds K hζ b p η
  have h :
      ‖h1EnergyMass (InfinitePlace K) (sourceKPCompactH1Localization K hζ b p η u)‖ ≤
        C * ‖sourceKPCompactH1Mass K hζ u‖ := by
    refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
      (p := fun v => ‖h1EnergyMass (InfinitePlace K) (sourceKPCompactH1Localization K hζ b p η v)‖ ≤
        C * ‖sourceKPCompactH1Mass K hζ v‖) u ?_ ?_
    · exact isClosed_le ((h1EnergyMass (InfinitePlace K)).continuous.comp
        (sourceKPCompactH1Localization K hζ b p η).continuous).norm
        ((sourceKPCompactH1Mass K hζ).continuous.norm.const_mul C)
    · intro f
      rw [sourceKPCompactH1Mass_core,sourceKPCompactH1Localization_core,
        ← sourceKPCompactCoreLocalizationLinear_apply]
      exact hbound f
  rw [hu,norm_zero,mul_zero] at h
  apply h1EnergyMass_injective (ι := InfinitePlace K)
  rw [map_zero]
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

end
end ArtinMatthews
