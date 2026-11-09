module

public import ArtinMatthews.SLocalFieldNorm
public import ArtinMatthews.AllowedIdealExtension


set_option backward.privateInPublic true
@[expose] public section

/-! The induced product-formula S-norm is the literal quotient
cardinality on every exterior integral ideal. The equality is proved
first on actual exterior primes, then by ideal factorization. -/

namespace ArtinMatthews.AllowedGenerators
open NumberField IsDedekindDomain SUnitGroup FractionalIdeal SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical BigOperators nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def integralExtendedNorm {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) : (Ideal (𝓞 K))⁰ →* ℝ :=
  (idealSNorm K hζ S₀).comp ((extendedIdealGroup K S₀).comp (FractionalIdeal.mk0 K))

theorem integralExtendedNorm_prime {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))
    (hP : P ∉ sourceHilbertSet K S₀) :
    integralExtendedNorm K hζ S₀ ⟨P.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr P.ne_bot⟩ =
      Ideal.absNorm P.asIdeal := by
  obtain ⟨a, ha⟩ := exists_exterior_prime_generator (sourceHilbertSeed K S₀) P hP
  let aK : Kˣ := Units.mk0 (a : K)
    (Subtype.coe_injective.ne (exterior_generator_ne_zero (sourceHilbertSeed K S₀) P a ha))
  have hgen : toPrincipalIdeal (sourceRing K S₀) K aK = extendedIdealGroup K S₀
      (FractionalIdeal.mk0 K ⟨P.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr P.ne_bot⟩) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, extendedIdealGroup_integral]
    have ha' : P.asIdeal.map (algebraMap (𝓞 K) (sourceRing K S₀)) =
        Ideal.span {show sourceRing K S₀ from a} := ha
    change spanSingleton (sourceRing K S₀)⁰ (aK : K) =
      (P.asIdeal.map (algebraMap (𝓞 K) (sourceRing K S₀)) : FractionalIdeal (sourceRing K S₀)⁰ K)
    rw [ha', coeIdeal_span_singleton]
    rfl
  change idealSNorm K hζ S₀ (extendedIdealGroup K S₀
    (FractionalIdeal.mk0 K ⟨P.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr P.ne_bot⟩)) =
      (Ideal.absNorm P.asIdeal : ℝ)
  exact (idealSNorm_eq_of_generator K hζ S₀ _ aK hgen).trans
    (fieldSNorm_exterior_prime_generator K (sourceHilbertSeed K S₀) P hP a ha)

theorem integralExtendedNorm_coprime {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (𝓞 K))⁰)
    (hc : IsCoprime I.val (Ideal.span {principalizingDenominator (sourceHilbertSeed K S₀)})) :
    integralExtendedNorm K hζ S₀ I = Ideal.absNorm I.val := by
  let d := principalizingDenominator (sourceHilbertSeed K S₀)
  let f := integralExtendedNorm K hζ S₀
  have hAll : ∀ J : Ideal (𝓞 K), ∀ hJ : J ≠ 0, IsCoprime J (Ideal.span {d}) →
      f ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ⟩ = (Ideal.absNorm J : ℝ) := by
    intro J
    refine UniqueFactorizationMonoid.induction_on_prime J ?_ ?_ ?_
    · intro hz _
      exact (hz rfl).elim
    · intro J hunit hJ _
      have hJ1 : J = 1 := (Ideal.isUnit_iff.mp hunit).trans Ideal.one_eq_top.symm
      subst J
      change f 1 = (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ)
      rw [map_one, map_one, Nat.cast_one]
    · intro A P hA hP ih hPA hcPA
      have hPcp := hcPA.of_mul_left_left
      have hAcp := hcPA.of_mul_left_right
      let p : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
      have hpS : p ∉ sourceHilbertSet K S₀ := by
        intro hpS
        have hno := (coprime_denominator_iff_exterior d
          (principalizingDenominator_ne_zero (sourceHilbertSeed K S₀)) P).mp hPcp p hpS
        exact hno dvd_rfl
      have hpNorm := integralExtendedNorm_prime K hζ S₀ p hpS
      have hfac : (⟨P * A, mem_nonZeroDivisors_iff_ne_zero.mpr hPA⟩ : (Ideal (𝓞 K))⁰) =
          ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr hP.ne_zero⟩ *
            ⟨A, mem_nonZeroDivisors_iff_ne_zero.mpr hA⟩ := rfl
      rw [hfac, map_mul, hpNorm, ih hA hAcp, map_mul, Nat.cast_mul]
  exact hAll I.val (mem_nonZeroDivisors_iff_ne_zero.mp I.property) hc

theorem idealSNorm_exterior_quotient_card {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (I : exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀))) :
    idealSNorm K hζ S₀ (extendedIdealGroup K S₀
      (FractionalIdeal.mk0 K ⟨I.val, mem_nonZeroDivisors_iff_ne_zero.mpr I.property.1⟩)) =
      (Nat.card ((sourceRing K S₀) ⧸ I.val.map (algebraMap (𝓞 K) (sourceRing K S₀))) : ℝ) := by
  rw [show Nat.card ((sourceRing K S₀) ⧸ I.val.map (algebraMap (𝓞 K) (sourceRing K S₀))) =
      Ideal.absNorm I.val from principal_quotient_card (sourceHilbertSeed K S₀) I.val I.property.2]
  exact integralExtendedNorm_coprime K hζ S₀
    ⟨I.val, mem_nonZeroDivisors_iff_ne_zero.mpr I.property.1⟩ I.property.2


def sourceExteriorEquiv (S₀ : Finset (HeightOneSpectrum (𝓞 K))) :
    exteriorIdeals (principalizingDenominator (sourceHilbertSeed K S₀)) ≃*
      (Ideal (sourceRing K S₀))⁰ :=
  principalExteriorIdealEquiv (sourceHilbertSeed K S₀)

theorem idealSNorm_integral_card {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (I : (Ideal (sourceRing K S₀))⁰) :
    idealSNorm K hζ S₀ (FractionalIdeal.mk0 K I) =
      (Nat.card ((sourceRing K S₀) ⧸ I.val) : ℝ) := by
  let J := (sourceExteriorEquiv K S₀).symm I
  have hmap : J.val.map (algebraMap (𝓞 K) (sourceRing K S₀)) = I.val :=
    congrArg Subtype.val ((sourceExteriorEquiv K S₀).apply_symm_apply I)
  have hfrac : extendedIdealGroup K S₀ (FractionalIdeal.mk0 K
        ⟨J.val, mem_nonZeroDivisors_iff_ne_zero.mpr J.property.1⟩) =
      FractionalIdeal.mk0 K I := by
    apply Units.ext
    exact (extendedIdealGroup_integral K S₀ _).trans
      (congrArg (fun T : Ideal (sourceRing K S₀) =>
        (T : FractionalIdeal (sourceRing K S₀)⁰ K)) hmap)
  have hcard := idealSNorm_exterior_quotient_card K hζ S₀ J
  rw [hfrac, hmap] at hcard
  exact hcard

end
end ArtinMatthews.AllowedGenerators
