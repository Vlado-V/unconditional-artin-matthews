module

public import ArtinMatthews.SIntegerLocalCZeroValues


set_option backward.privateInPublic true
@[expose] public section

/-! Fourier sums at arbitrary frequencies in the literal standard
S-integer source phase. No chosen coherent trace phase is substituted. -/
namespace ArtinMatthews.SIntegerFourier

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

def sourceGaussAt (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) : ℂ :=
  principalFourier a (a ^ n) (linearPowerPhase S₀ a (exterior_generator_ne_zero S₀ P a ha) n)
    (generatorResidueCharacter S₀ P hP a ha ξ) h

theorem sourceGaussAt_congr (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h h' : PrincipalIntegerRing S₀)
    (hh : h - h' ∈ Ideal.span {a * a ^ n}) :
    sourceGaussAt S₀ P hP a ha ξ n h = sourceGaussAt S₀ P hP a ha ξ n h' := by
  have he : Ideal.Quotient.mk (Ideal.span {a * a ^ n}) h = Ideal.Quotient.mk _ h' :=
    Ideal.Quotient.eq.mpr hh
  unfold sourceGaussAt principalFourier
  simp only [he]

theorem sourceGaussAt_zero_off_support (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (hbad : P ∉ traceBadPlaces K) (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ)
    (n : ℕ) (h : PrincipalIntegerRing S₀) (hh : ¬ a ^ n ∣ h) :
    sourceGaussAt S₀ P hP a ha ξ n h = 0 :=
  principalFourier_zero_off_support a (a ^ n) (exterior_generator_ne_zero S₀ P a ha) _
    (linearPowerPhase_primitive S₀ P hP a ha n hbad) _ h hh

theorem sourceGaussAt_lift (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ principalizingSet S₀) (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (ξ : MulChar ((𝓞 K) ⧸ P.asIdeal) ℂ) (n : ℕ) (h : PrincipalIntegerRing S₀) :
    sourceGaussAt S₀ P hP a ha ξ n (a ^ n * h) =
      (Ideal.absNorm P.asIdeal : ℂ) ^ n * residueTransformOnSource S₀ P hP a ha ξ 1 h := by
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a}) :=
    principal_element_quotient_finite S₀ a (exterior_generator_ne_zero S₀ P a ha)
  let : Finite ((PrincipalIntegerRing S₀) ⧸ Ideal.span {a * a ^ n}) :=
    principal_element_quotient_finite S₀ _ (mul_ne_zero (exterior_generator_ne_zero S₀ P a ha)
      (pow_ne_zero n (exterior_generator_ne_zero S₀ P a ha)))
  unfold sourceGaussAt
  rw [principalFourier_lift, linearPowerPhase_lower,
    linearReduction_kernel_card S₀ P hP a ha n, Nat.cast_pow]
  simp only [residueTransformOnSource, pow_one]

end
end ArtinMatthews.SIntegerFourier
