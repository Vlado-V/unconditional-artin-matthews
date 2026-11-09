module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyCoordinates
public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyCoordinatesBalanced


set_option backward.privateInPublic true
@[expose] public section

/-! Actual balanced representatives in the fixed ideal's integer basis.
Their coordinate map is injective and has a field/ideal dependent support bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def idealModuleIntegerElement (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) : I :=
  ⟨idealIntegerElement I hI a, idealIntegerElement_mem K I hI a⟩

theorem idealModuleIntegerElement_coe (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    ((idealModuleIntegerElement K I hI a).val : K) = (a.val : K) :=
  idealIntegerElement_coe I hI a

theorem idealModuleIntegerCoordinates_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (idealModuleIntegerCoordinates K I hI) := by
  intro a b h
  apply (mixedIntegralIdealBasis K I hI).repr.injective
  exact Finsupp.ext fun j => congrFun h j

theorem exists_balanced_idealModuleIntegerCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      ∃ a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
        relativeElementClassMap _ a = J ∧
          ‖fun j => (idealModuleIntegerCoordinates K I hI
            (idealModuleIntegerElement K I hI a) j : ℝ)‖ ≤
            C * (FractionalIdeal.absNorm J.val.val : ℝ) ^
              (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC, hbalance⟩ := exists_balanced_idealElementRepresentative_norm K
    (integralIdealFractionalUnit I hI)
  refine ⟨idealModuleIntegerCoordinateConstant K I hI * C,
    mul_pos (idealModuleIntegerCoordinateConstant_pos K I hI) hC, fun J => ?_⟩
  obtain ⟨a, ha, hb⟩ := hbalance J
  refine ⟨a, ha, ?_⟩
  have hc := idealModuleIntegerCoordinates_norm_le K I hI (idealModuleIntegerElement K I hI a)
  rw [idealModuleIntegerElement_coe] at hc
  exact hc.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hb (idealModuleIntegerCoordinateConstant_pos K I hI).le)

def idealModuleBalancedCoordinateConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ℝ :=
  (exists_balanced_idealModuleIntegerCoordinates K I hI).choose

theorem idealModuleBalancedCoordinateConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < idealModuleBalancedCoordinateConstant K I hI :=
  (exists_balanced_idealModuleIntegerCoordinates K I hI).choose_spec.1

def idealModuleBalancedRepresentative (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    nonzeroIdealElements (integralIdealFractionalUnit I hI) :=
  ((exists_balanced_idealModuleIntegerCoordinates K I hI).choose_spec.2 J).choose

theorem idealModuleBalancedRepresentative_spec (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    relativeElementClassMap _ (idealModuleBalancedRepresentative K I hI J) = J :=
  ((exists_balanced_idealModuleIntegerCoordinates K I hI).choose_spec.2 J).choose_spec.1

theorem idealModuleBalancedRepresentative_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (idealModuleBalancedRepresentative K I hI) :=
  Function.LeftInverse.injective (idealModuleBalancedRepresentative_spec K I hI)

def idealModuleBalancedIntegerCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    IdealModuleFrequencyIndex K I hI → ℤ :=
  idealModuleIntegerCoordinates K I hI
    (idealModuleIntegerElement K I hI (idealModuleBalancedRepresentative K I hI J))

theorem idealModuleBalancedIntegerCoordinates_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (idealModuleBalancedIntegerCoordinates K I hI) := by
  intro J J' h
  have hi := idealModuleIntegerCoordinates_injective K I hI h
  apply idealModuleBalancedRepresentative_injective K I hI
  apply Subtype.ext
  apply Units.ext
  simpa only [idealModuleIntegerElement_coe] using congrArg (fun a : I => (a.val : K)) hi

theorem idealModuleBalancedIntegerCoordinates_norm_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    ‖fun j => (idealModuleBalancedIntegerCoordinates K I hI J j : ℝ)‖ ≤
      idealModuleBalancedCoordinateConstant K I hI *
        (FractionalIdeal.absNorm J.val.val : ℝ) ^ (1 / (Module.finrank ℚ K : ℝ)) :=
  ((exists_balanced_idealModuleIntegerCoordinates K I hI).choose_spec.2 J).choose_spec.2

end
end ArtinMatthews.VaryingKummerAnalytic
