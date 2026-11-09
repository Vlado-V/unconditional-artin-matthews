module

public import ArtinMatthews.PrincipalQuotientFourier
public import ArtinMatthews.SIntegerStandardPhase
public import ArtinMatthews.SIntegerFiniteQuotients
public import ArtinMatthews.SIntegerPhaseCongruence


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier support and exact lifting for the actual standard source
phase and actual exterior S-integer prime generators. Primitivity and
the Norm(P)^k multiplicity are derived from the frozen quotient packet. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceProductPowerPhase (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (n k : ℕ) :
    AddChar ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n * a ^ k}) ℂ :=
  sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n * a ^ k)
    (mul_ne_zero (pow_ne_zero n ha) (pow_ne_zero k ha))

theorem sourceProductPowerPhase_mk (a : PrincipalIntegerRing S₀) (ha : a ≠ 0)
    (n k : ℕ) (x : PrincipalIntegerRing S₀) :
    sourceProductPowerPhase S₀ a ha n k (Ideal.Quotient.mk _ x) =
      sCharacter K (principalizingSet S₀) ((x : K) / ((a : K)^n * (a : K)^k)) := by
  rw [sourceProductPowerPhase, sIntegerQuotientPhase_mk]
  rfl

theorem sourceProductPowerPhase_primitive (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n k : ℕ) (hbad : P ∉ traceBadPlaces K) :
    (sourceProductPowerPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) n k).IsPrimitive := by
  unfold sourceProductPowerPhase
  exact (sourcePhase_primitive_congr S₀ _ _ _ _ (pow_add a n k).symm).mpr
    (sIntegerQuotientPhase_primitive S₀ P hP a ha (n + k) hbad)

theorem sourceProductPowerPhase_lower (a : PrincipalIntegerRing S₀) (ha : a ≠ 0)
    (n k : ℕ) :
    quotientLowerChar (a ^ n) (a ^ k) (sourceProductPowerPhase S₀ a ha n k) =
      sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n) (pow_ne_zero n ha) := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientLowerChar_mk, sourceProductPowerPhase_mk, sIntegerQuotientPhase_mk]
  have haK : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
  congr 1
  change ((a : K) ^ k * (x : K)) / ((a : K) ^ n * (a : K) ^ k) =
    (x : K) / (a : K) ^ n
  field_simp

def sourceFourier (a : PrincipalIntegerRing S₀) (ha : a ≠ 0) (n k : ℕ)
    (F : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) → ℂ)
    (h : PrincipalIntegerRing S₀) : ℂ :=
  principalFourier (a ^ n) (a ^ k) (sourceProductPowerPhase S₀ a ha n k) F h

theorem sourceFourier_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n k : ℕ) (hbad : P ∉ traceBadPlaces K)
    (F : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) → ℂ)
    (h : PrincipalIntegerRing S₀)
    (hF : sourceFourier S₀ a (exterior_generator_ne_zero S₀ P a ha) n k F h ≠ 0) :
    h ∈ (P.asIdeal ^ k).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) := by
  rw [generator_power_ideal S₀ P a ha k, Ideal.mem_span_singleton]
  exact principalFourier_support (a^n) (a^k) (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))
    _ (sourceProductPowerPhase_primitive S₀ P hP a ha n k hbad) F h hF

theorem sourceFourier_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n k : ℕ) (hbad : P ∉ traceBadPlaces K)
    (F : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) → ℂ)
    (h : PrincipalIntegerRing S₀)
    (hh : h ∉ (P.asIdeal ^ k).map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    sourceFourier S₀ a (exterior_generator_ne_zero S₀ P a ha) n k F h = 0 := by
  by_contra hn
  exact hh (sourceFourier_support S₀ P hP a ha n k hbad F h hn)

theorem sourceReduction_kernel_card (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a}) (n k : ℕ) :
    Nat.card (quotientReduction (a ^ n) (a ^ k)).toAddMonoidHom.ker = Ideal.absNorm P.asIdeal ^ k := by
  have hc := AddSubgroup.card_ker_mul_card_of_surjective
    (f := (quotientReduction (a ^ n) (a ^ k)).toAddMonoidHom)
    (quotientReduction_surjective (a ^ n) (a ^ k))
  have hl : Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) = Ideal.absNorm P.asIdeal ^ n :=
    generatorQuotient_card S₀ P hP a ha n
  have hu : Nat.card ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n * a ^ k}) =
      Ideal.absNorm P.asIdeal ^ (n + k) := by
    rw [← pow_add]
    exact generatorQuotient_card S₀ P hP a ha (n + k)
  rw [hl, hu, pow_add] at hc
  have hpos : 0 < Ideal.absNorm P.asIdeal ^ n :=
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot)) n
  exact Nat.eq_of_mul_eq_mul_right hpos (hc.trans (Nat.mul_comm _ _))

theorem sourceFourier_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (n k : ℕ) (F : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) → ℂ)
    (h : PrincipalIntegerRing S₀) :
    sourceFourier S₀ a (exterior_generator_ne_zero S₀ P a ha) n k F (a ^ k * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ k *
        ∑' x : (PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}, F x *
          sIntegerQuotientPhase K (principalizingSet S₀) (a ^ n)
            (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)) (Ideal.Quotient.mk _ h * x) := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n}) :=
    principal_element_quotient_finite S₀ _ (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a ^ n * a ^ k}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))
      (pow_ne_zero k (exterior_generator_ne_zero S₀ P a ha)))
  unfold sourceFourier
  rw [principalFourier_lift, sourceProductPowerPhase_lower,
    sourceReduction_kernel_card S₀ P hP a ha n k, Nat.cast_pow]

end
end ArtinMatthews.SIntegerFourier
