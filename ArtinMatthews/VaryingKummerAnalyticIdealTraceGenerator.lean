module

public import ArtinMatthews.VaryingKummerAnalyticRayClassRepresentatives
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualLattice


set_option backward.privateInPublic true
@[expose] public section

/-! Actual trace-dual generators modulo arbitrary nonzero integral ideals.
Coprime ideal-class representatives supply the generator; no principal
different or globally principal modulus is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem exists_fractional_coprime_principal
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    ∃ (β : Kˣ) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥),
      IsCoprime J M ∧ toPrincipalIdeal (𝓞 K) K β = I * integralIdealFractionalUnit J hJ := by
  obtain ⟨Jn,hcop,hclass⟩ := exists_coprime_class_representative M hM (ClassGroup.mk K I)⁻¹
  have hJ : Jn.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp Jn.property
  have hc : ClassGroup.mk K (integralIdealFractionalUnit Jn.val hJ) =
      (ClassGroup.mk K I)⁻¹ := by
    change ClassGroup.mk K (FractionalIdeal.mk0 K Jn) = _
    rw [ClassGroup.mk_mk0]
    exact hclass
  let j : integralIdealClassFiber I :=
    ⟨integralIdealFractionalUnit Jn.val hJ, FractionalIdeal.coeIdeal_le_one, hc⟩
  let β := (idealElementRepresentative I j).val
  refine ⟨β,Jn.val,hJ,hcop,?_⟩
  have he := congrArg Subtype.val (idealElementRepresentative_spec I j)
  change toPrincipalIdeal (𝓞 K) K β * I⁻¹ = integralIdealFractionalUnit Jn.val hJ at he
  calc
    toPrincipalIdeal (𝓞 K) K β =
        (toPrincipalIdeal (𝓞 K) K β * I⁻¹) * I := by simp
    _ = _ := by rw [he,mul_comm]

omit [NumberField K] in
theorem integral_coe_mem_fractional_iff (I : Ideal (𝓞 K)) (a : 𝓞 K) :
    (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K) ↔ a ∈ I := by
  constructor
  · intro h
    obtain ⟨b,hb,hba⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp h
    exact NumberField.RingOfIntegers.coe_injective hba ▸ hb
  · exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰

theorem integral_mem_fractional_div_coprime
    (M J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (hcop : IsCoprime J M) (a : 𝓞 K) :
    (a : K) ∈ (M : FractionalIdeal (𝓞 K)⁰ K) / (J : FractionalIdeal (𝓞 K)⁰ K) ↔ a ∈ M := by
  rw [FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)]
  constructor
  · intro h
    obtain ⟨j,hj,m,hm,hjm⟩ := hcop.exists
    have hj' := h (j : K) (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ hj)
    have haj : a*j ∈ M := (integral_coe_mem_fractional_iff K M (a*j)).mp (by simpa using hj')
    have ham : a*m ∈ M := M.mul_mem_left a hm
    have he : a*j + a*m = a := by rw [← mul_add,hjm,mul_one]
    exact he ▸ M.add_mem haj ham
  · intro ha y hy
    obtain ⟨b,hb,rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    exact (integral_coe_mem_fractional_iff K M (a*b)).mpr (M.mul_mem_right b ha)

theorem exists_trace_modulus_generator (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) :
    ∃ β : Kˣ, ∀ a : 𝓞 K,
      ((a : K) ∈ FractionalIdeal.dual ℤ ℚ
        (toPrincipalIdeal (𝓞 K) K β).val ↔ a ∈ M) := by
  let m := integralIdealFractionalUnit M hM
  let I := mixedTraceDualIdeal K m
  obtain ⟨β,J,hJ,hcop,hβ⟩ := exists_fractional_coprime_principal K I M hM
  refine ⟨β,fun a => ?_⟩
  have hdual : FractionalIdeal.dual ℤ ℚ (toPrincipalIdeal (𝓞 K) K β).val =
      (M : FractionalIdeal (𝓞 K)⁰ K) / (J : FractionalIdeal (𝓞 K)⁰ K) := by
    have hβ' := congrArg Units.val hβ
    change (toPrincipalIdeal (𝓞 K) K β).val =
      FractionalIdeal.dual ℤ ℚ m.val * (J : FractionalIdeal (𝓞 K)⁰ K) at hβ'
    rw [hβ', FractionalIdeal.dual_eq_mul_inv, mul_inv]
    rw [← mul_assoc, ← FractionalIdeal.dual_eq_mul_inv,
      FractionalIdeal.dual_dual]
    exact (div_eq_mul_inv _ _).symm
  rw [hdual]
  exact integral_mem_fractional_div_coprime K M J hJ hcop a

end
end ArtinMatthews.VaryingKummerAnalytic
