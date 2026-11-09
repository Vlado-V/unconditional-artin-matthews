module

public import ArtinMatthews.SourceCRTInverseCofactor


set_option backward.privateInPublic true
@[expose] public section

/-! Primitivity of the actual standard phase at a product of distinct
exterior prime powers.  The inverse-cofactor units remain explicit in
the component proof, including zero exponents. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (A : ι → Type*) [∀ i, CommRing (A i)]

omit [Fintype ι] in
theorem probePiAddChar_primitive_of_components (ψ : AddChar (∀ i, A i) ℂ)
    (hψ : ∀ i, (probePiAddCharComponent A ψ i).IsPrimitive) : ψ.IsPrimitive := by
  intro x hx he
  have hz : x = 0 := by
    funext i
    by_contra hi
    apply hψ i hi
    ext y
    have ht := congrArg (fun φ : AddChar (∀ i, A i) ℂ => φ (Pi.single i y)) he
    have hm : x * Pi.single i y = Pi.single i (x i * y) := by
      ext j
      by_cases hij : i = j
      · subst j; simp
      · simp only [Pi.mul_apply, Pi.single_eq_of_ne' hij, mul_zero]
    change ψ (Pi.single i (x i * y)) = 1
    simpa only [AddChar.mulShift_apply, AddChar.one_apply, hm] using ht
  exact hx hz

omit [Fintype ι] in
theorem probeCRTAddChar_primitive_of_components {B : Type*} [CommRing B]
    (e : B ≃+* ∀ i, A i) (ψ : AddChar B ℂ)
    (hψ : ∀ i, (probeCRTAddCharComponent A e ψ i).IsPrimitive) : ψ.IsPrimitive := by
  have hp : (ψ.compAddMonoidHom e.symm.toAddMonoidHom).IsPrimitive :=
    probePiAddChar_primitive_of_components A _ hψ
  have ht := probeAddChar_transport_primitive e
    (ψ.compAddMonoidHom e.symm.toAddMonoidHom) hp
  have he : (ψ.compAddMonoidHom e.symm.toAddMonoidHom).compAddMonoidHom
      e.toAddMonoidHom = ψ := by
    ext x
    exact congrArg ψ (e.symm_apply_apply x)
  rw [he] at ht
  exact ht

end
end ArtinMatthews.VaryingKummerAnalytic

namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sourcePrimePowerPhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n : ℕ) (hbad : P ∉ traceBadPlaces K) :
    (sourcePrimePowerPhase S₀ P a ha n).IsPrimitive :=
  pullAddChar_primitive _ _ (sIntegerQuotientPhase_primitive S₀ P hP a ha n hbad)

theorem sourcePrimeComponent_primitive (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (hbad : ∀ i, P i ∉ traceBadPlaces K) (i : ι) :
    (sourcePrimeComponent S₀ P hP a ha n i).IsPrimitive := by
  rw [sourcePrimeComponent_eq_inverseShift S₀ P hP a ha n i]
  exact probe_addChar_primitive_unit_shift _
    (sourcePrimePowerPhase_primitive S₀ (P i) (hS i) (a i) (ha i) (n i) (hbad i)) _

theorem sourceProductCRTPhase_primitive (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (hbad : ∀ i, P i ∉ traceBadPlaces K) :
    (sourceCRTPhase S₀ P n (∏ j, a j ^ n j) (generatorProduct_ne_zero S₀ P a ha n)
      (crtModulus_generator S₀ P n a ha)).IsPrimitive :=
  probeCRTAddChar_primitive_of_components _ (primeCRTEquiv S₀ P n hP) _
    (sourcePrimeComponent_primitive S₀ P hP hS a ha n hbad)

theorem sourceProductQuotientPhase_primitive (P : ι → HeightOneSpectrum (𝓞 K))
    (hP : Pairwise fun i j => P i ≠ P j) (hS : ∀ i, P i ∉ principalizingSet S₀)
    (a : ι → PrincipalIntegerRing S₀)
    (ha : ∀ i, (P i).asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a i})
    (n : ι → ℕ) (hbad : ∀ i, P i ∉ traceBadPlaces K) :
    (sIntegerQuotientPhase K (principalizingSet S₀) (∏ j, a j ^ n j)
      (generatorProduct_ne_zero S₀ P a ha n)).IsPrimitive := by
  let e := Ideal.quotEquivOfEq (crtModulus_generator S₀ P n a ha)
  have hp := sourceProductCRTPhase_primitive S₀ P hP hS a ha n hbad
  have ht := pullAddChar_primitive e.symm _ hp
  have he : pullAddChar e.symm
      (sourceCRTPhase S₀ P n (∏ j, a j ^ n j) (generatorProduct_ne_zero S₀ P a ha n)
        (crtModulus_generator S₀ P n a ha)) =
      sIntegerQuotientPhase K (principalizingSet S₀) (∏ j, a j ^ n j)
        (generatorProduct_ne_zero S₀ P a ha n) := by
    ext x
    change sIntegerQuotientPhase K (principalizingSet S₀) (∏ j, a j ^ n j)
        (generatorProduct_ne_zero S₀ P a ha n) (e (e.symm x)) = _
    rw [e.apply_symm_apply]
  rw [he] at ht
  exact ht

end
end ArtinMatthews.SourceCRTNormalization
