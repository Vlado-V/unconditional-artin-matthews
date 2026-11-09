module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualComparison
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The actual conductor-twisted trace-dual class permutation, including
denominator clearing of its generally nonintegral representatives. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)

def mixedPrimitiveDualClassEquiv : ClassGroup (𝓞 K) ≃ ClassGroup (𝓞 K) where
  toFun c := ClassGroup.mk K (mixedTraceDualIdeal K 1) *
    (ClassGroup.mk K (integralIdealFractionalUnit M hM))⁻¹ * c⁻¹
  invFun c := ClassGroup.mk K (mixedTraceDualIdeal K 1) *
    (ClassGroup.mk K (integralIdealFractionalUnit M hM))⁻¹ * c⁻¹
  left_inv c := by simp [mul_comm,mul_left_comm]
  right_inv c := by simp [mul_comm,mul_left_comm]

variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

theorem mixedPrimitiveDualIntegralIdeal_fractional :
    (mixedPrimitiveDualIntegralIdeal K I M : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (((mixedPrimitiveDualFractionalIdeal K I M).den : 𝓞 K) : K) *
        mixedPrimitiveDualFractionalIdeal K I M :=
  (mixedPrimitiveDualFractionalIdeal K I M).den_mul_self_eq_num'.symm

/-- Clearing the actual denominator preserves the ideal class of dual(MI). -/
theorem mixedPrimitiveDualIntegralIdeal_class :
    ClassGroup.mk K (integralIdealFractionalUnit (mixedPrimitiveDualIntegralIdeal K I M)
      (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM)) =
      ClassGroup.mk K (mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM)) := by
  let d : Kˣ := Units.mk0
    (((mixedPrimitiveDualFractionalIdeal K I M).den : 𝓞 K) : K)
    (by exact_mod_cast nonZeroDivisors.coe_ne_zero (mixedPrimitiveDualFractionalIdeal K I M).den)
  have h : integralIdealFractionalUnit (mixedPrimitiveDualIntegralIdeal K I M)
      (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM) =
      toPrincipalIdeal (𝓞 K) K d * mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM) := by
    apply Units.ext
    change (mixedPrimitiveDualIntegralIdeal K I M : FractionalIdeal (𝓞 K)⁰ K) =
      (toPrincipalIdeal (𝓞 K) K d : FractionalIdeal (𝓞 K)⁰ K) * _
    rw [coe_toPrincipalIdeal]
    exact mixedPrimitiveDualIntegralIdeal_fractional K M I
  rw [h,map_mul]
  have hp : ClassGroup.mk K (toPrincipalIdeal (𝓞 K) K d) = 1 := by
    apply ClassGroup.mk_eq_one_iff.mpr
    rw [coe_toPrincipalIdeal,FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨(d : K),rfl⟩⟩
  rw [hp,one_mul]

/-- The integral representative actually lands in the conductor-twisted
dual class, and these classes form a genuine involutive permutation. -/
theorem mixedPrimitiveDualIntegralIdeal_class_permutation :
    ClassGroup.mk K (integralIdealFractionalUnit (mixedPrimitiveDualIntegralIdeal K I M)
      (mixedPrimitiveDualIntegralIdeal_ne_bot K I M hI hM)) =
      mixedPrimitiveDualClassEquiv K M hM
        (ClassGroup.mk K (integralIdealFractionalUnit I hI)) := by
  rw [mixedPrimitiveDualIntegralIdeal_class K M hM I hI, mixedTraceDualIdeal_class]
  have h : mixedConductorIdeal K I M hI hM =
      integralIdealFractionalUnit M hM * integralIdealFractionalUnit I hI := by
    apply Units.ext
    exact FractionalIdeal.coeIdeal_mul M I
  rw [h,map_mul,mul_inv]
  simp only [mixedPrimitiveDualClassEquiv,Equiv.coe_fn_mk,mul_assoc]

end
end ArtinMatthews.VaryingKummerAnalytic
