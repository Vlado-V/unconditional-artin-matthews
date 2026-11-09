module

public import ArtinMatthews.VaryingKummerAnalyticGaussianSieveEmbedding
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyBalanced


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine coordinate Gaussian sieve on arbitrary fixed number-field
ideals, with literal trace characters and the actual primitive modulus labels. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem idealModule_coordinatePhase_eq_trace (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (α : K) (a : I) :
    coordinatePhase (idealModuleTraceCoordinates K I hI α) (idealModuleIntegerCoordinates K I hI a) =
      idealModuleTraceChar K I α a := by
  rw [coordinatePhase,idealModuleTraceChar_apply,fieldTraceAddChar_apply]
  have ht := idealModuleTrace_pairing_eq_sum K I hI a α
  have hc : (Algebra.trace ℚ K (α*(a.val:K)) : ℂ) =
      ((∑ j, (idealModuleIntegerCoordinates K I hI a j : ℝ)*
        idealModuleTraceCoordinates K I hI α j : ℝ):ℂ) := by exact_mod_cast ht
  rw [hc]
  push_cast
  congr 1
  simp only [mul_comm]
  ring

def idealModuleSieveReciprocalRadius (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (U : ℝ) : ℝ :=
  max 1 (1/idealModuleCoordinateSeparationRadius K I hI U)

theorem idealModuleSieveReciprocalRadius_one_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (U : ℝ) :
    1 ≤ idealModuleSieveReciprocalRadius K I hI U := le_max_left _ _

theorem idealModule_modular_additive_sieve (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    {U H : ℝ} (hU : 0 < U) (hH : 0 < H)
    (P : Finset (IdealFrequencyLabel K))
    (hP : ∀ ℓ ∈ P, (Ideal.absNorm ℓ.1.val : ℝ) ≤ U)
    (A : Finset I)
    (hA : ∀ a ∈ A, (∑ j, (idealModuleIntegerCoordinates K I hI a j:ℝ)^2) ≤ H^2)
    (v : I → ℂ) :
    (∑ ℓ ∈ P, ‖∑ a ∈ A, v a *
      idealModuleTraceChar K I (idealModuleFrequencyLabelValue K I hI ℓ) a‖^2) ≤
    (coordinateOptimizedSieveConstant (IdealModuleFrequencyIndex K I hI)*
      (H^(Module.finrank ℚ K)+(idealModuleSieveReciprocalRadius K I hI U)^(Module.finrank ℚ K)))*
        ∑ a ∈ A, ‖v a‖^2 := by
  have hrad := idealModuleCoordinateSeparationRadius_pos K I hI hU
  have hsmall : 1/idealModuleSieveReciprocalRadius K I hI U ≤
      idealModuleCoordinateSeparationRadius K I hI U := by
    have H' := one_div_le_one_div_of_le (one_div_pos.mpr hrad)
      (le_max_right 1 (1/idealModuleCoordinateSeparationRadius K I hI U))
    simpa only [idealModuleSieveReciprocalRadius,one_div_one_div] using H'
  have hsep : ∀ ℓ ∈ P, ∀ ℓ' ∈ P, ℓ ≠ ℓ' → ∀ k : IdealModuleFrequencyIndex K I hI → ℤ,
      1/idealModuleSieveReciprocalRadius K I hI U ≤
        ‖(fun j => idealModuleLabelCoordinates K I hI ℓ j -
          idealModuleLabelCoordinates K I hI ℓ' j+(k j:ℝ))‖ := by
    intro ℓ hℓ ℓ' hℓ' hne k
    exact hsmall.trans (idealModuleLabel_coordinates_separation K I hI hne k (hP ℓ hℓ) (hP ℓ' hℓ'))
  have H' := coordinate_modular_primal_sieve_embedding
    (idealModuleSieveReciprocalRadius_one_le K I hI U) hH P
    (idealModuleLabelCoordinates K I hI) hsep A (idealModuleIntegerCoordinates K I hI)
    (idealModuleIntegerCoordinates_injective K I hI) hA v
  simpa only [idealModuleLabelCoordinates,idealModule_coordinatePhase_eq_trace,
    idealModuleFrequencyIndex_card] using H'

end
end ArtinMatthews.VaryingKummerAnalytic
