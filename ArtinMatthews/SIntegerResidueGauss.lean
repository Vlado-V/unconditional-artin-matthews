module

public import ArtinMatthews.SIntegerGaussCRT
public import ArtinMatthews.SIntegerSexticTransport
public import ArtinMatthews.ProbeSexticGaussPhase
public import ArtinMatthews.SIntegerPhaseCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine finite-field Gauss data in the literal standard generator
phase. This is obtained through the proved full quotient equivalence,
with no independent additive-phase or Gauss-value hypothesis. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def residueSourcePhase (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) :
    AddChar ((𝓞 K) ⧸ P.asIdeal) ℂ :=
  pullAddChar (generatorResidueEquiv S₀ P hP a ha).symm
    (sIntegerQuotientPhase K (principalizingSet S₀) a (exterior_generator_ne_zero S₀ P a ha))

theorem residueSourcePhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) : (residueSourcePhase S₀ P hP a ha).IsPrimitive := by
  apply pullAddChar_primitive
  exact (sourcePhase_primitive_congr S₀ _ _ _ _ (pow_one a).symm).mpr
    (sIntegerQuotientPhase_primitive S₀ P hP a ha 1 hbad)

theorem residueSourcePhase_ne_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) : residueSourcePhase S₀ P hP a ha ≠ 1 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  intro he
  apply residueSourcePhase_primitive S₀ P hP a ha hbad (one_ne_zero : (1 : (𝓞 K) ⧸ P.asIdeal) ≠ 0)
  rw [AddChar.mulShift_one, he]

theorem residueSourcePhase_mk (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (x : 𝓞 K) :
    residueSourcePhase S₀ P hP a ha (Ideal.Quotient.mk _ x) =
      localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) ((x : K) / (a : K)))) := by
  rw [residueSourcePhase, pullAddChar_apply]
  have hm := generatorResidueEquiv_mk S₀ P hP a ha x
  rw [← hm, RingEquiv.symm_apply_apply, sIntegerQuotientPhase_mk]
  change sCharacter K (principalizingSet S₀) ((x : K) / (a : K)) = _
  have h := sCharacter_prime_power K (principalizingSet S₀) P hP
    (generatorFieldUnit S₀ P a ha)
    (fun Q hQ hQP => exterior_generator_other_valuation S₀ P a ha Q hQ hQP)
    1 x (fun Q _ => Q.valuation_le_one x)
  change sCharacter K (principalizingSet S₀) ((x : K) / (a : K) ^ 1) =
    localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) ((x : K) / (a : K) ^ 1))) at h
  simpa only [pow_one] using h

def residueSourceTau (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) : ℂ :=
  ∑' z : (𝓞 K) ⧸ P.asIdeal, χ z * residueSourcePhase S₀ P hP a ha z

theorem residueSourceTau_principal (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) : residueSourceTau S₀ P hP a ha 1 = -1 := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  simpa only [residueSourceTau, tsum_fintype, gaussSum] using
    gaussSum_one_left (residueSourcePhase_ne_one S₀ P hP a ha hbad)

theorem residueSourceTau_norm (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (hχ : χ ≠ 1) :
    ‖residueSourceTau S₀ P hP a ha χ‖ = Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [residueSourceTau, tsum_fintype, gaussSum, hc] using
    primitive_gaussSum_norm χ (primitiveOnIdeals_of_field χ hχ)
      (residueSourcePhase S₀ P hP a ha) (residueSourcePhase_primitive S₀ P hP a ha hbad)

theorem residueSourceTau_inverse_pair (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (hminus : χ (-1) = 1) :
    residueSourceTau S₀ P hP a ha χ * residueSourceTau S₀ P hP a ha (χ^5) =
      (Ideal.absNorm P.asIdeal : ℂ) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  simpa only [residueSourceTau, tsum_fintype, gaussSum, hc] using
    probeSexticGauss_inverse_pair χ hχ hminus (residueSourcePhase S₀ P hP a ha)
      (residueSourcePhase_primitive S₀ P hP a ha hbad)

end
end ArtinMatthews.SIntegerFourier
