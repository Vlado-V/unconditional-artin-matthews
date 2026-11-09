module

public import ArtinMatthews.VaryingKummerAnalyticRayCharacterQuotient
public import ArtinMatthews.VaryingKummerAnalyticRayFractionalDenominatorCount


set_option backward.privateInPublic true
@[expose] public section

/-! Actual descent of the ray ideal character to its residue conductor.
The kernel is proved trivial using genuine coprime integral fractions and
local congruences. The descended character agrees on all old prime-to
ideals and retains finite order. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField RayClass IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace EvenRayCharacter
variable {N : ℕ} [NeZero N] (ψ : EvenRayCharacter K N)

def conductorIdealProjection (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) :
    IdealRayClassGroup (rationalIdealRayModulus K N) →*
      IdealRayClassGroup (integralIdealRayModulus f hf) :=
  idealConductorProjection (integralIdealRayModulus_antitone (rationalModulusIdeal_ne_bot N) hf hMf)

theorem conductorIdealProjection_surjective (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) :
    Function.Surjective (conductorIdealProjection f hf hMf) :=
  idealConductorProjection_surjective _

theorem rayClassCharacter_conductor_kernel (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
      if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    (conductorIdealProjection f hf hMf).ker ≤ ψ.rayClassCharacter.ker := by
  intro c hc
  obtain ⟨I,rfl⟩ := QuotientGroup.mk'_surjective _ c
  obtain ⟨x,hx,hIx⟩ := (idealConductorProjection_ideal_eq_one_iff
    (integralIdealRayModulus_antitone (rationalModulusIdeal_ne_bot N) hf hMf) I).mp hc
  have hcounts : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ rationalModulusIdeal (𝓞 K) N →
      FractionalIdeal.count K v (spanSingleton (𝓞 K)⁰ (x:K)) = 0 := by
    intro v hv
    have H := I.property v ((integralIdealFiniteModulus_mem_support _ (rationalModulusIdeal_ne_bot N) v).mpr hv)
    rw [← hIx,coe_toPrincipalIdeal] at H
    exact H
  obtain ⟨a,b,ha,hb,hac,hbc,hab⟩ := exists_coprime_integral_fraction_of_counts K
    (rationalModulusIdeal (𝓞 K) N) (rationalModulusIdeal_ne_bot N) x hcounts
  have hmul : (b:K)*(x:K)=(a:K) := by
    have hbK : (b:K) ≠ 0 := by exact_mod_cast hb
    rw [hab]
    field_simp [hbK]
  have hd := principal_idealRayModulus_integral_difference f hf x hx a b hmul
  have he : Ideal.Quotient.mk f a = Ideal.Quotient.mk f b :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem a b).mpr hd
  have hva := hmask a
  have hvb := hmask b
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ a).mpr hac)] at hva
  rw [ite_eq_left ((quotient_isUnit_iff_span_coprime _ b).mpr hbc)] at hvb
  have hval : ψ.idealHom (integralIdealFractionalUnit (Ideal.span {a}) (by simpa using ha)) =
      ψ.idealHom (integralIdealFractionalUnit (Ideal.span {b}) (by simpa using hb)) := by
    apply Units.ext
    rw [ψ.principalLaw a ha hac,ψ.principalLaw b hb hbc,hva,hvb,he]
  change ψ.idealHom (I:FractionalIdealGroup K) = 1
  rw [← hIx,toPrincipalIdeal_eq_fraction x a b ha hb hab,map_div,hval]
  simp

def descendedIdealRayCharacter (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
      if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    IdealRayClassGroup (integralIdealRayModulus f hf) →* ℂˣ :=
  (QuotientGroup.lift (conductorIdealProjection f hf hMf).ker ψ.rayClassCharacter
    (ψ.rayClassCharacter_conductor_kernel f hf hMf φ hmask)).comp
      (QuotientGroup.quotientKerEquivOfSurjective (conductorIdealProjection f hf hMf)
        (conductorIdealProjection_surjective f hf hMf)).symm.toMonoidHom

theorem descendedIdealRayCharacter_projection (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
      if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
        then φ (Ideal.Quotient.mk f a) else 0)
    (c : IdealRayClassGroup (rationalIdealRayModulus K N)) :
    ψ.descendedIdealRayCharacter f hf hMf φ hmask (conductorIdealProjection f hf hMf c) =
      ψ.rayClassCharacter c := by
  let p := conductorIdealProjection f hf hMf
  let e := QuotientGroup.quotientKerEquivOfSurjective p (conductorIdealProjection_surjective f hf hMf)
  have he : e (QuotientGroup.mk' p.ker c) = p c := rfl
  change (QuotientGroup.lift p.ker ψ.rayClassCharacter
    (ψ.rayClassCharacter_conductor_kernel f hf hMf φ hmask)) (e.symm (p c)) = _
  rw [← he,MulEquiv.symm_apply_apply]
  rfl

theorem descendedIdealRayCharacter_finiteOrder (f : Ideal (𝓞 K)) (hf : f ≠ ⊥)
    (hMf : rationalModulusIdeal (𝓞 K) N ≤ f) (φ : MulChar ((𝓞 K) ⧸ f) ℂ)
    (hmask : ∀ a : 𝓞 K, ψ.residue (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a) =
      if IsUnit (Ideal.Quotient.mk (rationalModulusIdeal (𝓞 K) N) a)
        then φ (Ideal.Quotient.mk f a) else 0) :
    ∃ e : ℕ, 0 < e ∧ ∀ c, ψ.descendedIdealRayCharacter f hf hMf φ hmask c ^ e = 1 := by
  obtain ⟨e,he,h⟩ := ψ.rayClassCharacter_finiteOrder
  refine ⟨e,he,fun c => ?_⟩
  obtain ⟨d,rfl⟩ := conductorIdealProjection_surjective f hf hMf c
  rw [ψ.descendedIdealRayCharacter_projection]
  exact h d

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
