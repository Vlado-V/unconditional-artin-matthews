module

public import ArtinMatthews.VaryingKummerAnalyticRayPrimitiveDescent


set_option backward.privateInPublic true
@[expose] public section

/-! The descended character has the actual primitive residue principal law.
The proof moves an ideal through the genuine ray-class projection and clears
its generator away from the original modulus. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def integralPrincipalPrimeToIdeal (M : Ideal (𝓞 K)) (hM : M ≠ ⊥)
    (a : 𝓞 K) (ha : a ≠ 0) (hcop : IsCoprime (Ideal.span {a}) M) :
    primeToModulusIdeals (integralIdealRayModulus M hM) :=
  ⟨toPrincipalIdeal (𝓞 K) K (Units.mk0 (a:K) (by exact_mod_cast ha)), by
    intro v hv
    have hd := (integralIdealFiniteModulus_mem_support M hM v).mp hv
    have hn : a ∉ v.asIdeal := fun h =>
      v.prime.not_isUnit (hcop.isUnit_of_dvd' (Ideal.dvd_span_singleton.mpr h) hd)
    rw [IdeleGroup.count_toPrincipalIdeal]
    have he : v.valuation K (a:K) = 1 := v.valuation_eq_one_iff_notMem.mpr hn
    simp only [Units.val_mk0,he,WithZero.log_one,neg_zero]⟩

namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

theorem descendedIdealRayCharacter_principal (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
      if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
        then φ (Ideal.Quotient.mk f a) else 0)
    (a : 𝓞 K) (ha : a ≠ 0) (hac : IsCoprime (Ideal.span {a}) f) :
    (ψ.descendedIdealRayCharacter f hf hMf φ hmask
      (QuotientGroup.mk' (principalRayIdealSubgroup (integralIdealRayModulus f hf))
        (integralPrincipalPrimeToIdeal f hf a ha hac)) : ℂ) = φ (Ideal.Quotient.mk f a) := by
  let m := rationalIdealRayModulus K N
  let n := integralIdealRayModulus f hf
  let hnm : n ≤ m := integralIdealRayModulus_antitone (rationalModulusIdeal_ne_bot N) hf hMf
  let J := integralPrincipalPrimeToIdeal f hf a ha hac
  let q := QuotientGroup.mk' (principalRayIdealSubgroup n)
  obtain ⟨c,hc⟩ := conductorIdealProjection_surjective f hf hMf (q J)
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  have hp : q (primeToIdealConductorInclusion hnm I) = q J := by
    rw [← idealConductorProjection_ideal hnm I]
    exact hc
  have hmem : primeToIdealConductorInclusion hnm I / J ∈ principalRayIdealSubgroup n := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (primeToIdealConductorInclusion hnm I / J) = 1
    rw [map_div,hp]
    simp only [div_self']
  obtain ⟨x,hx,hIx⟩ := (mem_principalRayIdealSubgroup_iff n _).mp hmem
  let ua : Kˣ := Units.mk0 (a:K) (by exact_mod_cast ha)
  let y : Kˣ := x * ua
  have hyI : toPrincipalIdeal (𝓞 K) K y = (I:FractionalIdealGroup K) := by
    change toPrincipalIdeal (𝓞 K) K (x*ua) = _
    rw [map_mul,hIx]
    change ((I:FractionalIdealGroup K) / toPrincipalIdeal (𝓞 K) K ua) *
      toPrincipalIdeal (𝓞 K) K ua = _
    exact div_mul_cancel _ _
  have hcounts : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ rationalModulusIdeal (𝓞 K) N →
      FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (y:K)) = 0 := by
    intro v hv
    have H := I.property v ((integralIdealFiniteModulus_mem_support _ (rationalModulusIdeal_ne_bot N) v).mpr hv)
    rw [← hyI,coe_toPrincipalIdeal] at H
    exact H
  obtain ⟨b,d,hb,hd,hbc,hdc,hy⟩ := exists_coprime_integral_fraction_of_counts K
    (rationalModulusIdeal (𝓞 K) N) (rationalModulusIdeal_ne_bot N) y hcounts
  have hmul : ((a*d:𝓞 K):K)*(x:K)=(b:K) := by
    have hdK : (d:K) ≠ 0 := by exact_mod_cast hd
    have H : (x:K)*(a:K)=(b:K)/(d:K) := hy
    have H' := (eq_div_iff hdK).mp H
    change ((a:K)*(d:K))*(x:K)=(b:K)
    calc
      ((a:K)*(d:K))*(x:K) = ((x:K)*(a:K))*(d:K) := by ring
      _ = (b:K) := H'
  have hdiff := principal_idealRayModulus_integral_difference f hf x hx b (a*d) hmul
  have he : Ideal.Quotient.mk f b = Ideal.Quotient.mk f a * Ideal.Quotient.mk f d := by
    rw [← map_mul]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem b (a*d)).mpr hdiff
  have hvb := hmask b
  have hvd := hmask d
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ b).mpr hbc)] at hvb
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ d).mpr hdc)] at hvd
  have hdunit : IsUnit (Ideal.Quotient.mk f d) := by
    simpa only [Ideal.Quotient.factor_mk] using
      ((quotient_isUnit_iff_span_coprime _ d).mpr hdc).map (Ideal.Quotient.factor hMf)
  have hval : (ψ.idealHom (I:FractionalIdealGroup K):ℂ) = φ (Ideal.Quotient.mk f a) := by
    rw [← hyI,toPrincipalIdeal_eq_fraction y b d hb hd hy,map_div,Units.val_div_eq_div_val,
      ψ.principalLaw b hb hbc,ψ.principalLaw d hd hdc,hvb,hvd,he,map_mul]
    exact mul_div_cancel_right₀ _ (MulChar.apply_ne_zero_iff.mpr hdunit)
  rw [← hc,ψ.descendedIdealRayCharacter_projection,ψ.rayClassCharacter_ideal]
  exact hval

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
