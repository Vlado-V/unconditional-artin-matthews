module

public import ArtinMatthews.SIntegerResidueGauss


set_option backward.privateInPublic true
@[expose] public section

/-! Exact residue transforms in the actual standard source phase,
including the positive-modulus trivial-character mask. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def residueTransformOnSource (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (v : ℕ) (h : PrincipalIntegerRing S₀) : ℂ :=
  ∑' z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
    (generatorResidueCharacter S₀ P hP a ha χ ^ v) z *
      sIntegerQuotientPhase K (principalizingSet S₀) a (exterior_generator_ne_zero S₀ P a ha)
        (Ideal.Quotient.mk _ h * z)

theorem residueTransformOnSource_transport (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (v : ℕ) (h : PrincipalIntegerRing S₀) :
    residueTransformOnSource S₀ P hP a ha χ v h =
      ∑' z : (𝓞 K) ⧸ P.asIdeal, (χ^v) z *
        residueSourcePhase S₀ P hP a ha (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ h) * z) := by
  let e := generatorResidueEquiv S₀ P hP a ha
  have hp (z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :
      sIntegerQuotientPhase K (principalizingSet S₀) a (exterior_generator_ne_zero S₀ P a ha)
        (Ideal.Quotient.mk _ h * z) =
      residueSourcePhase S₀ P hP a ha (e (Ideal.Quotient.mk _ h) * e z) := by
    change _ = sIntegerQuotientPhase K (principalizingSet S₀) a (exterior_generator_ne_zero S₀ P a ha)
      (e.symm (e (Ideal.Quotient.mk _ h) * e z))
    rw [← map_mul e, e.symm_apply_apply]
  unfold residueTransformOnSource
  calc
    _ = ∑' z : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a},
        (χ^v) (e z) * residueSourcePhase S₀ P hP a ha (e (Ideal.Quotient.mk _ h) * e z) := by
      apply tsum_congr
      intro z
      rw [hp, generatorResidueCharacter, ← pullCharacter_pow, pullCharacter_apply]
    _ = _ := e.toEquiv.tsum_eq (fun z : (𝓞 K) ⧸ P.asIdeal =>
      (χ^v) z * residueSourcePhase S₀ P hP a ha (e (Ideal.Quotient.mk _ h) * z))

theorem residueTransformOnSource_one (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (v : ℕ) :
    residueTransformOnSource S₀ P hP a ha χ v 1 = residueSourceTau S₀ P hP a ha (χ^v) := by
  rw [residueTransformOnSource_transport]
  simp only [map_one, one_mul, residueSourceTau]

theorem residueTransformOnSource_sixth (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (χ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (hχ : orderOf χ = 6) (v : ℕ) (h : PrincipalIntegerRing S₀) :
    residueTransformOnSource S₀ P hP a ha χ v h =
      if h ∈ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) then
        (if 6 ∣ v then (Ideal.absNorm P.asIdeal : ℂ) - 1 else 0)
      else (χ^v)⁻¹ (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ h)) *
        residueSourceTau S₀ P hP a ha (χ^v) := by
  let : Field ((𝓞 K) ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : Finite ((𝓞 K) ⧸ P.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  let : Fintype ((𝓞 K) ⧸ P.asIdeal) := Fintype.ofFinite _
  have hc : Fintype.card ((𝓞 K) ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hz : generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ h) = 0 ↔
      h ∈ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
    rw [ha]
    constructor
    · intro he
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      exact (generatorResidueEquiv S₀ P hP a ha).injective (he.trans (map_zero _).symm)
    · intro he
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr he, map_zero]
  rw [residueTransformOnSource_transport]
  simpa only [probeResidueGauss, residueSourceTau, tsum_fintype, gaussSum, hc, hz] using
    probeResidueGauss_sixth χ hχ (residueSourcePhase S₀ P hP a ha)
      (residueSourcePhase_ne_one S₀ P hP a ha hbad) v
      (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ h))

end
end ArtinMatthews.SIntegerFourier
