module

public import ArtinMatthews.VaryingKummerAnalyticIdealFrequencyCoordinates
public import ArtinMatthews.VaryingKummerAnalyticMixedBalancedElements
public import ArtinMatthews.VaryingKummerAnalyticRayIdealCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! Balanced ideal generators have controlled actual integer coordinates in
the same ring-of-integers basis used by all conductor frequencies. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem idealIntegerCoordinates_injective : Function.Injective (idealIntegerCoordinates K) := by
  intro a b h
  apply (NumberField.RingOfIntegers.basis K).repr.injective
  exact Finsupp.ext fun j => congrFun h j

theorem idealIntegerElement_mem (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (a : nonzeroIdealElements (integralIdealFractionalUnit I hI)) :
    idealIntegerElement I hI a ∈ I :=
  ((FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp a.property).choose_spec.1

theorem exists_balanced_idealIntegerCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : integralIdealClassFiber (integralIdealFractionalUnit I hI),
      ∃ a : nonzeroIdealElements (integralIdealFractionalUnit I hI),
        relativeElementClassMap _ a = J ∧
          ‖fun j => (idealIntegerCoordinates K (idealIntegerElement I hI a) j : ℝ)‖ ≤
            C * (FractionalIdeal.absNorm J.val.val : ℝ) ^
              (1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC, hbalance⟩ := exists_balanced_idealElementRepresentative_norm K
    (integralIdealFractionalUnit I hI)
  refine ⟨idealIntegerCoordinateConstant K * C,
    mul_pos (idealIntegerCoordinateConstant_pos K) hC, fun J => ?_⟩
  obtain ⟨a, ha, hb⟩ := hbalance J
  refine ⟨a, ha, ?_⟩
  have hcoords := idealIntegerCoordinates_norm_le K (idealIntegerElement I hI a)
  rw [idealIntegerElement_coe] at hcoords
  exact hcoords.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hb (idealIntegerCoordinateConstant_pos K).le)

/-- The coordinate bound depends only on the field and the fixed integral
ideal, uniformly over all ideals in the corresponding inverse class. -/
def idealBalancedCoordinateConstant (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ℝ :=
  (exists_balanced_idealIntegerCoordinates K I hI).choose

theorem idealBalancedCoordinateConstant_pos (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < idealBalancedCoordinateConstant K I hI :=
  (exists_balanced_idealIntegerCoordinates K I hI).choose_spec.1

/-- Actual balanced generators, selected from the proved existence theorem. -/
def balancedIdealCoordinateRepresentative (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    nonzeroIdealElements (integralIdealFractionalUnit I hI) :=
  ((exists_balanced_idealIntegerCoordinates K I hI).choose_spec.2 J).choose

theorem balancedIdealCoordinateRepresentative_spec (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    relativeElementClassMap _ (balancedIdealCoordinateRepresentative K I hI J) = J :=
  ((exists_balanced_idealIntegerCoordinates K I hI).choose_spec.2 J).choose_spec.1

theorem balancedIdealCoordinateRepresentative_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (balancedIdealCoordinateRepresentative K I hI) :=
  Function.LeftInverse.injective (balancedIdealCoordinateRepresentative_spec K I hI)

/-- Distinct ideals are represented by distinct integer vectors in the
common ring-of-integers basis. -/
def balancedIdealIntegerCoordinates (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    IdealFrequencyCoordinateIndex K → ℤ :=
  idealIntegerCoordinates K
    (idealIntegerElement I hI (balancedIdealCoordinateRepresentative K I hI J))

theorem balancedIdealIntegerCoordinates_injective (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    Function.Injective (balancedIdealIntegerCoordinates K I hI) := by
  intro J J' h
  have hi := idealIntegerCoordinates_injective K h
  apply balancedIdealCoordinateRepresentative_injective K I hI
  apply Subtype.ext
  apply Units.ext
  simpa only [idealIntegerElement_coe] using congrArg (fun a : 𝓞 K => (a : K)) hi

theorem balancedIdealIntegerCoordinates_norm_le (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (J : integralIdealClassFiber (integralIdealFractionalUnit I hI)) :
    ‖fun j => (balancedIdealIntegerCoordinates K I hI J j : ℝ)‖ ≤
      idealBalancedCoordinateConstant K I hI *
        (FractionalIdeal.absNorm J.val.val : ℝ) ^ (1 / (Module.finrank ℚ K : ℝ)) :=
  ((exists_balanced_idealIntegerCoordinates K I hI).choose_spec.2 J).choose_spec.2

end
end ArtinMatthews.VaryingKummerAnalytic
