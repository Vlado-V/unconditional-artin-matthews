module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualRelativeMultiplication
public import ArtinMatthews.VaryingKummerAnalyticRayIdealMultiplicativity


set_option backward.privateInPublic true
@[expose] public section

/-! Arithmetic coherence of the primitive theta transform across all ideal
classes. The single norm-one scalar is constructed from the base class and
actual residue coordinates; no common root number is assumed. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
set_option maxHeartbeats 800000
variable (K : Type*) [Field K] [NumberField K]
variable (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)

def idealTopResidueOne : (𝓞 K) ⧸ M :=
  idealResidueCoordinate ⊤ M top_ne_bot hM (⟨1,by trivial⟩ : (⊤ : Ideal (𝓞 K)))

theorem idealTopResidueOne_isUnit : IsUnit (idealTopResidueOne K M hM) := by
  apply (idealResidueCoordinate_isUnit_iff ⊤ M top_ne_bot hM
    (⟨1,by trivial⟩ : (⊤ : Ideal (𝓞 K))) ⊤ (by simp)).mpr
  rw [← Ideal.one_eq_top]
  exact isCoprime_one_left

variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

theorem idealModuleDualResidue_generator_top
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) :
    idealModuleDualResidue K I M hI hM β β.property =
      idealModuleDualResidue K ⊤ M top_ne_bot hM
        (idealModuleGeneratorDualTop K I M hI hM β)
        (idealModuleGeneratorDualTop K I M hI hM β).property * idealTopResidueOne K M hM := by
  exact idealModuleDualResidue_generator K M hM I hI β

theorem mixedPrimitiveDualRelativeCoefficient_generator
    (ψ : EvenIdealRayCharacter K M) (hMt : M ≠ ⊤)
    (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (hGM : IsCoprime G M)
    (hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0) :
    ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K ⊤ M top_ne_bot hM
      (idealModuleGeneratorDualTop K I M hI hM β)
      (idealModuleGeneratorDualTop_ne_zero K I M hI hM hMt β hβ)) =
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ)⁻¹ *
        ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ) := by
  let A := mixedPrimitiveDualRelativeIdeal K ⊤ M top_ne_bot hM
    (idealModuleGeneratorDualTop K I M hI hM β)
    (idealModuleGeneratorDualTop_ne_zero K I M hI hM hMt β hβ)
  let B := mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ
  have H : EvenRayCharacter.underlyingIdeal A = G * EvenRayCharacter.underlyingIdeal B := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    change (EvenRayCharacter.underlyingIdeal A : FractionalIdeal (𝓞 K)⁰ K) =
      ((G * EvenRayCharacter.underlyingIdeal B : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [FractionalIdeal.coeIdeal_mul,EvenRayCharacter.underlyingIdeal_coe,
      EvenRayCharacter.underlyingIdeal_coe]
    exact congrArg Units.val
      (mixedPrimitiveDualRelativeIdeal_generator_val K I M hI hM hMt G hG hprod β hβ)
  change ψ.inverse.coefficient A = _ * ψ.inverse.coefficient B
  rw [← ψ.inverse.allCoefficient_underlying A,H,
    ψ.inverse.allCoefficient_mul_of_coprime G _ hG hGM,
    ψ.inverse.allCoefficient_underlying B]
  rw [EvenIdealRayCharacter.inverse_idealHom,Units.val_inv_eq_inv_val]

/-- One actual norm-one scalar works for every ideal class simultaneously.
It converts the primal class coefficient times the transformed finite
residue weight into the inverse ray-character coefficient. -/
theorem mixedPrimitiveTheta_common_scalar (ψ : EvenIdealRayCharacter K M) (hMt : M ≠ ⊤) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
      (G : Ideal (𝓞 K)) (hG : G ≠ ⊥) (_hGM : IsCoprime G M)
      (_hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
      (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0),
      (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
        ψ.residue⁻¹ (idealModuleDualResidue K I M hI hM β β.property) =
          ε * ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ) := by
  let : Finite ((𝓞 K) ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  let : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _
  obtain ⟨κ,hκ,Hκ⟩ := mixedPrimitiveDualRay_relativeCoefficient_exists_scalar K ⊤ M top_ne_bot hM ψ
  have hκ0 : κ ≠ 0 := by intro h; simp [h] at hκ
  let r := ψ.residue⁻¹ (idealTopResidueOne K M hM)
  have hr : ‖r‖ = 1 := by
    let hu := idealTopResidueOne_isUnit K M hM
    change ‖ψ.residue⁻¹ (idealTopResidueOne K M hM)‖ = 1
    rw [← hu.unit_spec]
    exact Complex.norm_eq_one_of_mem_rootsOfUnity ((ψ.residue⁻¹).apply_mem_rootsOfUnity hu.unit)
  refine ⟨r*κ⁻¹,by rw [norm_mul,norm_inv,hr,hκ,inv_one,mul_one],?_⟩
  intro I hI G hG hGM hprod β hβ
  let γ := idealModuleGeneratorDualTop K I M hI hM β
  have hγ := idealModuleGeneratorDualTop_ne_zero K I M hI hM hMt β hβ
  have H := (Hκ γ hγ).symm.trans
    (mixedPrimitiveDualRelativeCoefficient_generator K M hM I hI ψ hMt G hG hGM hprod β hβ)
  have Hw : ψ.residue⁻¹ (idealModuleDualResidue K ⊤ M top_ne_bot hM γ γ.property) =
      κ⁻¹ * ((ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ)⁻¹ *
        ψ.inverse.coefficient (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ)) := by
    rw [← H,← mul_assoc,inv_mul_cancel₀ hκ0,one_mul]
  rw [idealModuleDualResidue_generator_top,map_mul]
  change (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) *
    (ψ.residue⁻¹ (idealModuleDualResidue K ⊤ M top_ne_bot hM γ γ.property) * r) = _
  rw [Hw]
  have hg0 : (ψ.idealHom (integralIdealFractionalUnit G hG) : ℂ) ≠ 0 := Units.ne_zero _
  field_simp

end
end ArtinMatthews.VaryingKummerAnalytic
