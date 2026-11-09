module

public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaRelativePacket
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaDualGenerator
public import ArtinMatthews.VaryingKummerAnalyticMixedPrimitiveThetaPrimalScalar
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDualClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplying a dual element by the fixed module generator multiplies
its actual relative ideal by the genuine coprime generator quotient. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hM : M ≠ ⊥)

def idealModuleGeneratorDualTop
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) :
    (mixedPrimitiveDualFractionalIdeal K ⊤ M).val :=
  ⟨(β : K) * (idealModuleGenerator I M hI hM : 𝓞 K),by
    change (β : K) * (idealModuleGenerator I M hI hM : 𝓞 K) ∈
      dual ℤ ℚ ((M*⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [Ideal.mul_top]
    exact (idealModuleGeneratorDualMap K M hM I hI β).property⟩

theorem idealModuleGeneratorDualTop_ne_zero (hMt : M ≠ ⊤)
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0) :
    (idealModuleGeneratorDualTop K I M hI hM β : K) ≠ 0 := by
  apply mul_ne_zero hβ
  exact_mod_cast idealModuleGenerator_ne_zero I M hI hM hMt

theorem mixedPrimitiveDualIdeal_mul_original :
    mixedTraceDualIdeal K (mixedConductorIdeal K ⊤ M top_ne_bot hM) =
      mixedTraceDualIdeal K (mixedConductorIdeal K I M hI hM) *
        integralIdealFractionalUnit I hI := by
  have htop : mixedConductorIdeal K ⊤ M top_ne_bot hM = integralIdealFractionalUnit M hM := by
    apply Units.ext
    change ((M*⊤ : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = (M : FractionalIdeal (𝓞 K)⁰ K)
    rw [Ideal.mul_top]
  have hmul : mixedConductorIdeal K I M hI hM =
      integralIdealFractionalUnit M hM * integralIdealFractionalUnit I hI := by
    apply Units.ext
    exact FractionalIdeal.coeIdeal_mul M I
  rw [htop,hmul,
    mixedTraceDualIdeal_eq_mul_inv K (integralIdealFractionalUnit M hM),
    mixedTraceDualIdeal_eq_mul_inv K (integralIdealFractionalUnit M hM * integralIdealFractionalUnit I hI)]
  simp [mul_assoc]

/-- An equality of the full fractional ideal units, so it can be applied to
the actual ideal-character homomorphism before deleting conductor primes. -/
theorem mixedPrimitiveDualRelativeIdeal_generator_val (hMt : M ≠ ⊤)
    (G : Ideal (𝓞 K)) (hG : G ≠ ⊥)
    (hprod : Ideal.span {idealModuleGenerator I M hI hM} = I*G)
    (β : (mixedPrimitiveDualFractionalIdeal K I M).val) (hβ : (β : K) ≠ 0) :
    (mixedPrimitiveDualRelativeIdeal K ⊤ M top_ne_bot hM
      (idealModuleGeneratorDualTop K I M hI hM β)
      (idealModuleGeneratorDualTop_ne_zero K I M hI hM hMt β hβ)).val =
      integralIdealFractionalUnit G hG * (mixedPrimitiveDualRelativeIdeal K I M hI hM β hβ).val := by
  let g : Kˣ := Units.mk0 (idealModuleGenerator I M hI hM : 𝓞 K)
    (by exact_mod_cast idealModuleGenerator_ne_zero I M hI hM hMt)
  have hg : toPrincipalIdeal (𝓞 K) K g =
      integralIdealFractionalUnit I hI * integralIdealFractionalUnit G hG := by
    apply Units.ext
    rw [Units.val_mul,coe_toPrincipalIdeal]
    change spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (idealModuleGenerator I M hI hM)) = _
    rw [← FractionalIdeal.coeIdeal_span_singleton,hprod,FractionalIdeal.coeIdeal_mul]
    rfl
  change relativeElementIdeal _ (Units.mk0 _ _) = integralIdealFractionalUnit G hG *
    relativeElementIdeal _ (Units.mk0 (β : K) hβ)
  have he : Units.mk0 (idealModuleGeneratorDualTop K I M hI hM β : K)
      (idealModuleGeneratorDualTop_ne_zero K I M hI hM hMt β hβ) = Units.mk0 (β : K) hβ * g := by
    apply Units.ext
    rfl
  rw [he,relativeElementIdeal,map_mul,hg,mixedPrimitiveDualIdeal_mul_original K I M hI hM]
  simp [relativeElementIdeal,mul_comm,mul_left_comm,mul_assoc]

end
end ArtinMatthews.VaryingKummerAnalytic
