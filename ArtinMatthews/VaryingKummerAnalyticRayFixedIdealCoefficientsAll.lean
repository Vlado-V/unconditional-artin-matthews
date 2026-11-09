module

public import ArtinMatthews.VaryingKummerAnalyticRayFixedIdealCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The conductor-one case and the unconditional fixed-ideal coefficient
identity for every positive rational modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {N : ℕ} [NeZero N]
namespace EvenRayCharacter
variable (ψ : EvenRayCharacter K N)

theorem exists_fixedIdeal_coefficient_residue_of_top
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (hMtop : rationalModulusIdeal (𝓞 K) N = ⊤) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (rationalModulusIdeal (𝓞 K) N)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (rationalModulusIdeal (𝓞 K) N)
        hI (rationalModulusIdeal_ne_bot N) a) := by
  let M := rationalModulusIdeal (𝓞 K) N
  have hM : M ≠ ⊥ := rationalModulusIdeal_ne_bot N
  have hcop (J : Ideal (𝓞 K)) : IsCoprime J M := by
    rw [show M = ⊤ from hMtop,← Ideal.one_eq_top]
    exact isCoprime_one_right
  have hquot (r : 𝓞 K) : Ideal.Quotient.mk M r = 1 := by
    rw [← map_one (Ideal.Quotient.mk M)]
    apply Ideal.Quotient.eq.mpr
    rw [show M = ⊤ from hMtop]
    trivial
  have hcoord (a : I) : idealResidueCoordinate I M hI hM a = 1 := by
    obtain ⟨r,hr⟩ := Ideal.Quotient.mk_surjective (idealResidueCoordinate I M hI hM a)
    rw [← hr,hquot]
  refine ⟨(ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)⁻¹,?_,fun J hJ a ha hprod => ?_⟩
  · rw [norm_inv,ψ.idealHom_norm,inv_one]
  · rw [ite_eq_left (hcop J),hcoord a,map_one,mul_one]
    have haspan : Ideal.span {(a:𝓞 K)} ≠ ⊥ := by
      simpa only [ne_eq,Ideal.span_singleton_eq_bot] using ha
    have hu : integralIdealFractionalUnit (Ideal.span {(a:𝓞 K)}) haspan =
        integralIdealFractionalUnit I hI * integralIdealFractionalUnit J hJ := by
      apply Units.ext
      change (Ideal.span {(a:𝓞 K)} : FractionalIdeal (𝓞 K)⁰ K) =
        (I : FractionalIdeal (𝓞 K)⁰ K)*(J : FractionalIdeal (𝓞 K)⁰ K)
      rw [hprod,FractionalIdeal.coeIdeal_mul]
    have H := ψ.principalLaw (a:𝓞 K) ha (hcop (Ideal.span {(a:𝓞 K)}))
    rw [hu,map_mul,Units.val_mul,hquot,map_one] at H
    have H' := congrArg (fun z : ℂ => (ψ.idealHom (integralIdealFractionalUnit I hI) : ℂ)⁻¹*z) H
    simpa only [← mul_assoc,inv_mul_cancel₀ (Units.ne_zero _),one_mul,mul_one] using H'

/-- Exact coefficients on any fixed nonzero ideal representative. The
multiplier has norm one, independently of the ideal J and its generator. -/
theorem exists_fixedIdeal_coefficient_residue
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥)
      (a : I) (_ha : (a:𝓞 K) ≠ 0) (_hprod : Ideal.span {(a:𝓞 K)} = I*J),
      (if IsCoprime J (rationalModulusIdeal (𝓞 K) N)
        then (ψ.idealHom (integralIdealFractionalUnit J hJ) : ℂ) else 0) =
      κ * ψ.residue (idealResidueCoordinate I (rationalModulusIdeal (𝓞 K) N)
        hI (rationalModulusIdeal_ne_bot N) a) := by
  by_cases hM : rationalModulusIdeal (𝓞 K) N = ⊤
  · exact ψ.exists_fixedIdeal_coefficient_residue_of_top I hI hM
  · exact ψ.exists_fixedIdeal_coefficient_residue_of_proper I hI hM

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
