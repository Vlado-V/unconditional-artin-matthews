module

public import ArtinMatthews.VaryingKummerAnalyticRayIdealModulus
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominator
public import ArtinMatthews.VaryingKummerAnalyticRayConductorCharacter


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite-order ray ideal character attached to the existing
integral principal law. Denominators and local congruences are discharged
with proved number-field objects. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def rationalIdealRayModulus (K : Type*) [Field K] [NumberField K] (N : ℕ) [NeZero N] : Modulus K :=
  integralIdealRayModulus (rationalModulusIdeal (𝓞 K) N) (rationalModulusIdeal_ne_bot N)

theorem toPrincipalIdeal_eq_fraction (x : Kˣ) (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : (x:K)=(a:K)/(b:K)) :
    toPrincipalIdeal (𝓞 K) K x =
      integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha) /
        integralIdealFractionalUnit (Ideal.span {b}) (by simpa using hb) := by
  apply Units.ext
  rw [coe_toPrincipalIdeal,Units.val_div_eq_div_val]
  change spanSingleton (𝓞 K)⁰ (x:K) =
    (Ideal.span {a} : FractionalIdeal (𝓞 K)⁰ K) / (Ideal.span {b} : FractionalIdeal (𝓞 K)⁰ K)
  rw [coeIdeal_span_singleton,coeIdeal_span_singleton,spanSingleton_div_spanSingleton,hab]

namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem idealHom_principal_ray (x : Kˣ)
    (hx : IdeleGroup.principalIdele K x ∈ idelePrimeToModulusSubgroup (rationalIdealRayModulus K N)) :
    ψ.idealHom (toPrincipalIdeal (𝓞 K) K x) = 1 := by
  obtain ⟨a,b,ha,hb,hac,hbc,hab⟩ := exists_coprime_integral_fraction_of_local_units K
    (rationalModulusIdeal (𝓞 K) N) (rationalModulusIdeal_ne_bot N) x
    (principal_idealRayModulus_valuation_one _ _ x hx)
  have hmul : (b:K)*(x:K)=(a:K) := by
    have hbK : (b:K) ≠ 0 := by exact_mod_cast hb
    rw [hab]
    field_simp [hbK]
  have hd := principal_idealRayModulus_integral_difference _ _ x hx a b hmul
  have he : Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a =
      Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hd
  have hc : ψ.idealHom (integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha)) =
      ψ.idealHom (integralIdealFractionalUnit (Ideal.span {b}) (by simpa using hb)) := by
    apply Units.ext
    rw [ψ.principalLaw a ha hac,ψ.principalLaw b hb hbc,he]
  rw [toPrincipalIdeal_eq_fraction x a b ha hb hab,map_div,hc]
  simp

def rayClassCharacter : IdealRayClassGroup (rationalIdealRayModulus K N) →* ℂˣ :=
  QuotientGroup.lift (principalRayIdealSubgroup (rationalIdealRayModulus K N))
    (ψ.idealHom.comp (primeToModulusIdeals (rationalIdealRayModulus K N)).subtype) (by
      intro I hI
      obtain ⟨x,hx,he⟩ := (mem_principalRayIdealSubgroup_iff _ I).mp hI
      change ψ.idealHom (I:FractionalIdealGroup K) = 1
      rw [← he]
      exact ψ.idealHom_principal_ray x hx)

theorem rayClassCharacter_ideal (I : primeToModulusIdeals (rationalIdealRayModulus K N)) :
    ψ.rayClassCharacter (QuotientGroup.mk' (principalRayIdealSubgroup (rationalIdealRayModulus K N)) I) =
      ψ.idealHom (I:FractionalIdealGroup K) := rfl

theorem rayClassCharacter_finiteOrder :
    ∃ e : ℕ, 0 < e ∧ ∀ c, ψ.rayClassCharacter c ^ e = 1 := by
  obtain ⟨e,he,heq⟩ := ψ.finiteOrder
  refine ⟨e,he,fun c => ?_⟩
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  exact heq I

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
