module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealRetraction


set_option backward.privateInPublic true
@[expose] public section

/-! Finite-order even ray characters at genuine integral ideal moduli.
Their full ideal homomorphisms and their principal laws are constructed
from the actual ideal ray class characters, rather than assumed as a
conductor descent input. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def integralIdealPrimeToIdeal (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hcop : IsCoprime I M) :
    primeToModulusIdeals (integralIdealRayModulus M hM) :=
  ⟨integralIdealFractionalUnit I hI,by
    intro v hv
    have hd := (integralIdealFiniteModulus_mem_support M hM v).mp hv
    have hn : ¬ v.asIdeal ∣ I := fun h => v.prime.not_isUnit (hcop.isUnit_of_dvd' h hd)
    change FractionalIdeal.count K v (I:FractionalIdeal (𝓞 K)⁰ K) = 0
    rw [FractionalIdeal.count_coe K v hI]
    have he : (Associates.mk v.asIdeal).count (Associates.mk I).factors = 0 := by
      simpa only [not_not] using (Associates.count_ne_zero_iff_dvd hI v.irreducible).not.mpr hn
    exact_mod_cast he⟩

structure EvenIdealRayCharacter (K : Type*) [Field K] [NumberField K] (M : Ideal (𝓞 K)) where
  idealHom : FractionalIdealGroup K →* ℂˣ
  finiteOrder : ∃ e : ℕ, 0 < e ∧ ∀ J, idealHom J ^ e = 1
  residue : MulChar ((𝓞 K) ⧸ M) ℂ
  principalLaw : ∀ (a : 𝓞 K) (ha : a ≠ 0), IsCoprime (Ideal.span {a}) M →
    (idealHom (integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha)) : ℂ) =
      residue (Ideal.Quotient.mk M a)

namespace EvenIdealRayCharacter
variable {M : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K M)

theorem idealHom_norm (J : FractionalIdealGroup K) : ‖(ψ.idealHom J : ℂ)‖ = 1 := by
  obtain ⟨e,he,hpow⟩ := ψ.finiteOrder
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) he.ne').mp
  have H := congrArg (fun z : ℂˣ => ‖(z:ℂ)‖) (hpow J)
  simpa only [Units.val_pow_eq_pow_val,norm_pow,Units.val_one,norm_one] using H

theorem residue_unit (z : (𝓞 K)ˣ) : ψ.residue (Ideal.Quotient.mk M (z:𝓞 K)) = 1 := by
  have hspan : Ideal.span {(z:𝓞 K)} = ⊤ := Ideal.span_singleton_eq_top.mpr z.isUnit
  have hcop : IsCoprime (Ideal.span {(z:𝓞 K)}) M := by
    rw [hspan,← Ideal.one_eq_top]
    exact isCoprime_one_left
  have H := ψ.principalLaw (z:𝓞 K) z.ne_zero hcop
  simpa only [hspan,integralIdealFractionalUnit_top,map_one,Units.val_one] using H.symm

def ofIdealRayClass (hM : M ≠ ⊥) (χ : IdealRayClassGroup (integralIdealRayModulus M hM) →* ℂˣ)
    (hχ : ∃ e : ℕ, 0 < e ∧ ∀ c, χ c ^ e = 1) (φ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hprincipal : ∀ (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) M),
      (χ (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus M hM))
        (integralPrincipalPrimeToIdeal M hM a ha hac)) : ℂ) = φ (Ideal.Quotient.mk M a)) :
    EvenIdealRayCharacter K M where
  idealHom := idealRayCharacterExtension (integralIdealRayModulus M hM) χ
  finiteOrder := idealRayCharacterExtension_finiteOrder _ χ hχ
  residue := φ
  principalLaw a ha hac := by
    have he : integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha) =
        (integralPrincipalPrimeToIdeal M hM a ha hac : FractionalIdealGroup K) := by
      apply Units.ext
      change (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) =
        (toPrincipalIdeal (𝓞 K) K (Units.mk0 (a:K) (by exact_mod_cast ha)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [coe_toPrincipalIdeal]
      exact FractionalIdeal.coeIdeal_span_singleton a
    rw [he,idealRayCharacterExtension_primeTo]
    exact hprincipal a ha hac

theorem ofIdealRayClass_idealHom_primeTo (hM : M ≠ ⊥)
    (χ : IdealRayClassGroup (integralIdealRayModulus M hM) →* ℂˣ)
    (hχ : ∃ e : ℕ, 0 < e ∧ ∀ c, χ c ^ e = 1) (φ : MulChar ((𝓞 K) ⧸ M) ℂ)
    (hprincipal : ∀ (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) M),
      (χ (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus M hM))
        (integralPrincipalPrimeToIdeal M hM a ha hac)) : ℂ) = φ (Ideal.Quotient.mk M a))
    (I : primeToModulusIdeals (integralIdealRayModulus M hM)) :
    (ofIdealRayClass hM χ hχ φ hprincipal).idealHom (I:FractionalIdealGroup K) =
      χ (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus M hM)) I) :=
  idealRayCharacterExtension_primeTo _ χ I

end EvenIdealRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
