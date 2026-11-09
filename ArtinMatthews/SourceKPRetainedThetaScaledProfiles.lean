module

public import ArtinMatthews.SourceKPRetainedThetaProfile


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed label scalars and the zero profile preserve the smoothness
and two-ended estimates used by the reflected finite-family constructor. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory QuadraticWeil
open SourcePhysical VaryingKummerAnalytic
open scoped NumberField ContDiff
noncomputable section

def sourceReflectionFiniteProfileInputs {V : Type*} (P : V → ℝ → ℂ) : Prop :=
  (∀ v : V, ContDiff ℝ ∞ (fun x : ℝ => P v (Real.exp x))) ∧
    ∀ v : V, ∃ α : ℝ, 0 ≤ α ∧ ∀ A : ℝ, 0 < A →
      ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ 2, ∀ x : ℝ,
        ‖iteratedFDeriv ℝ k (fun y => P v (Real.exp y)) x‖ ≤
          M * min (Real.exp (α * x)) (Real.exp (-A * x))

theorem sourceReflectionFiniteProfileInputs_const_mul {V : Type*} (P : V → ℝ → ℂ)
    (c : V → ℂ) (hP : sourceReflectionFiniteProfileInputs P) :
    sourceReflectionFiniteProfileInputs (fun v x => c v * P v x) := by
  rcases hP with ⟨hs, hb⟩
  refine ⟨fun v => contDiff_const.mul (hs v), fun v => ?_⟩
  obtain ⟨α, hα, h⟩ := hb v
  refine ⟨α, hα, fun A hA => ?_⟩
  obtain ⟨M, hM, hbound⟩ := h A hA
  refine ⟨‖c v‖ * M, mul_nonneg (norm_nonneg _) hM, fun k hk x => ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_mul_field, norm_mul,
    mul_assoc, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact mul_le_mul_of_nonneg_left (hbound k hk x) (norm_nonneg _)

def sourceReflectionOptionProfile {V : Type*} (P : V → ℝ → ℂ) : Option V → ℝ → ℂ
  | none => fun _ => 0
  | some v => P v

theorem sourceReflectionFiniteProfileInputs_option {V : Type*} (P : V → ℝ → ℂ)
    (hP : sourceReflectionFiniteProfileInputs P) :
    sourceReflectionFiniteProfileInputs (sourceReflectionOptionProfile P) := by
  rcases hP with ⟨hs, hb⟩
  constructor
  · intro v
    cases v with
    | none => exact contDiff_const
    | some v => exact hs v
  · intro v
    cases v with
    | none =>
      refine ⟨0, le_rfl, fun _ _ => ⟨0, le_rfl, fun k _ x => ?_⟩⟩
      simp [sourceReflectionOptionProfile]
    | some v => exact hb v

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {I : Type*} [Finite I]
variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
variable {J : Ideal (𝓞 K)} (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
variable (rowU : I → exteriorUnitSubgroup (sourceHilbertSet K S₀))
variable (a : I → ∀ P : ↥(sourceHilbertSet K S₀), SourceFiniteKP2Projective K hζ P.val)
variable (v : InfinitePlace K)
variable (U : ∀ P : ↥(sourceHilbertSet K S₀), SourceReflection.SourceThetaFiniteCutoff K P.val)

local notation "Label" => SourceKPRetainedThetaLabel K hζ S₀ I
local notation "P" => sourceKPRetainedThetaProfile K hζ S₀ hS η hJ rowU a v U

theorem sourceKPRetainedThetaProfile_scaled_inputs (c : Label → ℂ) :
    sourceReflectionFiniteProfileInputs (fun d x => c d * P d x) :=
  sourceReflectionFiniteProfileInputs_const_mul P c
    (sourceKPRetainedThetaProfile_finiteProfiles K hζ S₀ hS η hJ rowU a v U)

theorem sourceKPRetainedThetaProfile_scaledOption_inputs (c : Label → ℂ) :
    sourceReflectionFiniteProfileInputs (sourceReflectionOptionProfile (fun d x => c d * P d x)) :=
  sourceReflectionFiniteProfileInputs_option _
    (sourceKPRetainedThetaProfile_scaled_inputs K hζ S₀ hS η hJ rowU a v U c)

end
end ArtinMatthews
