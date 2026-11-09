module

public import ArtinMatthews.SIntegerHigherSourcePhase


set_option backward.privateInPublic true
@[expose] public section

/-! Exact quotient lifting for the literal higher source phase. The
congruence gate and its actual quotient are retained in the identity. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceHigherGauss (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n : ℕ) (H : PrincipalIntegerRing S₀) : ℂ :=
  oppositeFourier (a * a ^ m) (a * a ^ n)
    (sourceHigherPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) m n)
    (fun v => generatorResidueCharacter S₀ P hP a ha ξ (quotientReduction a (a ^ n) v)) H

theorem sourceHigherGauss_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (m n : ℕ) (H : PrincipalIntegerRing S₀) :
    sourceHigherGauss S₀ P hP a ha ξ m n ((a * a ^ m) * H) =
      (Nat.card (oppositeReduction (a * a ^ m) (a * a ^ n)).toAddMonoidHom.ker : ℂ) *
        sourceGaussAt S₀ P hP a ha ξ n H := by
  have ha0 := exterior_generator_ne_zero S₀ P a ha
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero ha0 (pow_ne_zero n ha0))
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(a * a ^ m) * (a * a ^ n)}) :=
    principal_element_quotient_finite S₀ _
      (mul_ne_zero (mul_ne_zero ha0 (pow_ne_zero m ha0)) (mul_ne_zero ha0 (pow_ne_zero n ha0)))
  unfold sourceHigherGauss
  rw [oppositeFourier_lift, sourceHigherPhase_lower]
  rfl

theorem sourceHigherGauss_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (m n : ℕ) (H : PrincipalIntegerRing S₀) (hH : ¬ a * a ^ m ∣ H) :
    sourceHigherGauss S₀ P hP a ha ξ m n H = 0 := by
  by_contra hh
  exact hH (oppositeFourier_support _ _
    (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha))) _
    (sourceHigherPhase_primitive S₀ P hP a ha hbad m n) _ H hh)

theorem sourceHigherGauss_quotient (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (m n : ℕ) (H : PrincipalIntegerRing S₀) :
    sourceHigherGauss S₀ P hP a ha ξ m n H =
      (Nat.card (oppositeReduction (a * a ^ m) (a * a ^ n)).toAddMonoidHom.ker : ℂ) *
        (if hH : a * a ^ m ∣ H then
          sourceGaussAt S₀ P hP a ha ξ n (principalDivide (a * a ^ m) H hH) else 0) := by
  by_cases hH : a * a ^ m ∣ H
  · rw [dite_eq_left hH]
    have hh := sourceHigherGauss_lift S₀ P hP a ha ξ m n
      (principalDivide (a * a ^ m) H hH)
    simpa only [← principalDivide_spec (a * a ^ m) H hH] using hh
  · rw [dite_eq_right hH, mul_zero,
      sourceHigherGauss_zero_off_support S₀ P hP a ha hbad ξ m n H hH]

end
end ArtinMatthews.SIntegerFourier
