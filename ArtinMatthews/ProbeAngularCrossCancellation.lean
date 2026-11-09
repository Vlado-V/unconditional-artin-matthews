module

public import ArtinMatthews.ProbeAngularResidueSymbol
public import ArtinMatthews.ProbeSexticCrossExponent


set_option backward.privateInPublic true
@[expose] public section

/-! Actual sextic cross-prime cancellation for integral exterior
generators in an explicitly S-isotropic subgroup. Their existence, the
source's complementary subgroup B, and S-integral phase comparisons are
not asserted by this module. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain KummerTheory GlobalClassFieldTheory.Reciprocity
open AlgebraicNumberTheory.PowerResidueSymbols ArtinMatthews.AngularLambda
open OAI OAI.ActualEisensteinCubic OAI.ConcreteTraceCRT
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [Algebra BaseField K]

structure ProbeIntegralExteriorGenerator (S : Finset (HeightOneSpectrum (𝓞 K)))
    (B : Subgroup Kˣ) (P : HeightOneSpectrum (𝓞 K)) where
  value : 𝓞 K
  nonzero : value ≠ 0
  belongs : nonzeroIntegralFieldUnit K value nonzero ∈ B
  simple : idealPrimeMultiplicity K P (Ideal.span {value}) = 1
  exterior_unit : ∀ Q, Q ∉ S → Q ≠ P → value ∉ Q.asIdeal

omit [Algebra BaseField K] in
theorem probeExponentSupport_subset_of_six (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S) :
    powerResidueExponentFinitePlaces K probeSix ⊆ S := by
  intro P hP
  apply hS P
  have hd := (mem_powerResidueExponentFinitePlaces_iff K probeSix P).mp hP
  exact Ideal.dvd_span_singleton.mp hd

theorem probeAngularResidue_reciprocity (hmu : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a : ProbeIntegralExteriorGenerator K S B P) (b : ProbeIntegralExteriorGenerator K S B Q) :
    globalAngularResidueCharacter K P (fun h => hP (hS P h)) (Ideal.Quotient.mk P.asIdeal b.value) =
      globalAngularResidueCharacter K Q (fun h => hQ (hS Q h)) (Ideal.Quotient.mk Q.asIdeal a.value) := by
  let hp : (6 : 𝓞 K) ∉ P.asIdeal := fun h => hP (hS P h)
  let hq : (6 : 𝓞 K) ∉ Q.asIdeal := fun h => hQ (hS Q h)
  have hbP := b.exterior_unit P hP hPQ
  have haQ := a.exterior_unit Q hQ (Ne.symm hPQ)
  have hs := probePrimeResidue_reciprocity_integral K probeSix (by norm_num) hmu S
    (probeExponentSupport_subset_of_six K S hS) B hB P Q hPQ hP hQ
    (probePrimeNorm_coprime_six K P hp) (probePrimeNorm_coprime_six K Q hq)
    a.value b.value a.nonzero b.nonzero a.belongs b.belongs hbP haQ a.simple b.simple
    (by intro v hv hvP hvQ; exact ⟨a.exterior_unit v hv hvP, b.exterior_unit v hv hvQ⟩)
  have hroot := (probeAngularIntegralCharacter_eq_symbol K P hp hmu b.value hbP).trans
    (hs.trans (probeAngularIntegralCharacter_eq_symbol K Q hq hmu a.value haQ).symm)
  have hval := congrArg (fun z : rootsOfUnity 6 (𝓞 K) => ((z.1 : (𝓞 K)ˣ) : 𝓞 K)) hroot
  simp only [probeIntegralSixthRoot_val] at hval
  have hz := (FaithfulSMul.algebraMap_injective BaseIntegers (𝓞 K)) hval
  rw [probeAngularIntegralCharacter_complex, probeAngularIntegralCharacter_complex]
  exact congrArg eisEmbedding hz

def probeAngularCrossUnit (P : HeightOneSpectrum (𝓞 K)) (hsix : (6 : 𝓞 K) ∉ P.asIdeal)
    (a : 𝓞 K) (ha : a ∉ P.asIdeal) : ℂˣ :=
  (globalAngularResidueCharacter K P hsix).toUnitHom (primeIdealResidueUnit K P a ha)

theorem probeAngularCrossUnit_pow_six (P : HeightOneSpectrum (𝓞 K))
    (hsix : (6 : 𝓞 K) ∉ P.asIdeal) (a : 𝓞 K) (ha : a ∉ P.asIdeal) :
    probeAngularCrossUnit K P hsix a ha ^ 6 = 1 := by
  apply Units.ext
  have h := pow_orderOf_eq_one (globalAngularResidueCharacter K P hsix)
  rw [globalAngularResidueCharacter_order K P hsix] at h
  have hv := congrArg (fun χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ => χ (primeIdealResidueUnit K P a ha)) h
  simpa only [probeAngularCrossUnit, Units.val_pow_eq_pow_val, Units.val_one,
    MulChar.coe_toUnitHom, MulChar.pow_apply_coe, MulChar.one_apply_coe] using hv

theorem probeAngularCrossUnit_reciprocity (hmu : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a : ProbeIntegralExteriorGenerator K S B P) (b : ProbeIntegralExteriorGenerator K S B Q) :
    probeAngularCrossUnit K P (fun h => hP (hS P h)) b.value (b.exterior_unit P hP hPQ) =
      probeAngularCrossUnit K Q (fun h => hQ (hS Q h)) a.value (a.exterior_unit Q hQ (Ne.symm hPQ)) := by
  apply Units.ext
  exact probeAngularResidue_reciprocity K hmu S hS B hB P Q hPQ hP hQ a b

theorem probeAngularCross_pair_cancel (hmu : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) hmu S B)
    (P Q : HeightOneSpectrum (𝓞 K)) (hPQ : P ≠ Q) (hP : P ∉ S) (hQ : Q ∉ S)
    (a : ProbeIntegralExteriorGenerator K S B P) (b : ProbeIntegralExteriorGenerator K S B Q)
    (e l e' l' k k' : ℤ) :
    let z := probeAngularCrossUnit K P (fun h => hP (hS P h)) b.value (b.exterior_unit P hP hPQ)
    let z' := probeAngularCrossUnit K Q (fun h => hQ (hS Q h)) a.value (a.exterior_unit Q hQ (Ne.symm hPQ))
    z ^ ((e + 3*l) * k' + (e + 3*l-k) * (e' + 3*l')) *
      z' ^ ((e' + 3*l') * k + (e' + 3*l'-k') * (e + 3*l)) *
      (z^2 * z'^2) ^ (e * e') = 1 := by
  dsimp only
  rw [← probeAngularCrossUnit_reciprocity K hmu S hS B hB P Q hPQ hP hQ a b]
  let z := probeAngularCrossUnit K P (fun h => hP (hS P h)) b.value (b.exterior_unit P hP hPQ)
  change z ^ _ * z ^ _ * (z ^ (2 : ℕ) * z ^ (2 : ℕ)) ^ (e * e') = 1
  rw [← zpow_add, ← pow_add]
  have he : (e + 3*l) * k' + (e + 3*l-k) * (e' + 3*l') +
      ((e' + 3*l') * k + (e' + 3*l'-k') * (e + 3*l)) = 2*(e+3*l)*(e'+3*l') := by ring
  rw [he]
  change z ^ (2*(e+3*l)*(e'+3*l')) * (z ^ (4 : ℤ)) ^ (e*e') = 1
  rw [← zpow_mul]
  simpa only [mul_assoc] using
    probeCrossPair_zpow_eq_one z (probeAngularCrossUnit_pow_six K P _ _ _) e l e' l'

theorem probeAngularCross_finite_pairs_cancel {ι : Type*}
    (hmu : (primitiveRoots 6 K).Nonempty)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ P, (6 : 𝓞 K) ∈ P.asIdeal → P ∈ S)
    (B : Subgroup Kˣ)
    (hB : ProbeHilbertSIsotropic K probeSix (by norm_num) hmu S B)
    (P : ι → HeightOneSpectrum (𝓞 K)) (hP : ∀ i, P i ∉ S)
    (g : ∀ i, ProbeIntegralExteriorGenerator K S B (P i))
    (pairs : Finset (ι × ι)) (hpairs : ∀ p ∈ pairs, P p.1 ≠ P p.2)
    (e l k : ι → ℤ) :
    (∏ p : pairs,
      let hne := hpairs p.val p.property
      let z := probeAngularCrossUnit K (P p.val.1) (fun h => hP p.val.1 (hS (P p.val.1) h))
        (g p.val.2).value ((g p.val.2).exterior_unit (P p.val.1) (hP p.val.1) hne)
      let z' := probeAngularCrossUnit K (P p.val.2) (fun h => hP p.val.2 (hS (P p.val.2) h))
        (g p.val.1).value ((g p.val.1).exterior_unit (P p.val.2) (hP p.val.2) (Ne.symm hne))
      z ^ ((e p.val.1 + 3*l p.val.1)*k p.val.2 + (e p.val.1+3*l p.val.1-k p.val.1)*(e p.val.2+3*l p.val.2)) *
        z' ^ ((e p.val.2+3*l p.val.2)*k p.val.1 + (e p.val.2+3*l p.val.2-k p.val.2)*(e p.val.1+3*l p.val.1)) *
        (z^2*z'^2) ^ (e p.val.1*e p.val.2)) = 1 := by
  apply Finset.prod_eq_one
  intro p _hp
  exact probeAngularCross_pair_cancel K hmu S hS B hB (P p.val.1) (P p.val.2)
    (hpairs p.val p.property) (hP p.val.1) (hP p.val.2) (g p.val.1) (g p.val.2) _ _ _ _ _ _

end
end ArtinMatthews.VaryingKummerAnalytic
