module

public import ArtinMatthews.SourceElementExponents
public import ArtinMatthews.SIntegerPrimeCRT


set_option backward.privateInPublic true
@[expose] public section

/-! True local orders of u times the sixth power of a literal source
prime-generator product. No local-order vector is supplied as a premise. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SIntegerQuotient
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceFrequencyExponents (u : sourceRing F S₀) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) :
    sourceElementExponents F S₀ (u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6)
      (mul_ne_zero hu (pow_ne_zero 6 (sourcePrimeExponentGenerator_ne_zero F hζ S₀ r))) =
        sourceElementExponents F S₀ u hu + 6 • r := by
  rw [sourceElementExponents_mul F S₀ u _ hu
    (pow_ne_zero 6 (sourcePrimeExponentGenerator_ne_zero F hζ S₀ r)),
    sourceElementExponents_pow F S₀ _ (sourcePrimeExponentGenerator_ne_zero F hζ S₀ r) 6,
    sourceElementExponents_of_generator F S₀ hζ r]

theorem sourceFrequency_mem_primePower_iff (u : sourceRing F S₀) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) (n : ℕ) :
    u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 ∈
      (P.val.asIdeal ^ n).map (algebraMap (𝓞 F) (sourceRing F S₀)) ↔
        n ≤ sourceElementExponents F S₀ u hu P + 6 * r P := by
  rw [sourceElementExponents_mem_primePower_iff F S₀ hζ _
    (mul_ne_zero hu (pow_ne_zero 6 (sourcePrimeExponentGenerator_ne_zero F hζ S₀ r))),
    sourceFrequencyExponents F S₀ hζ u hu r]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

theorem sourceFrequency_exact_order (u : sourceRing F S₀) (hu : u ≠ 0)
    (r : SourcePrimeExponents F S₀) (P : SourceExteriorPrime F S₀) :
    u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 ∈
        primePowerIdeal (sourceHilbertSeed F S₀) P.val
          (sourceElementExponents F S₀ u hu P + 6 * r P) ∧
      u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 ∉
        primePowerIdeal (sourceHilbertSeed F S₀) P.val
          (sourceElementExponents F S₀ u hu P + 6 * r P + 1) := by
  have h (n : ℕ) : u * sourcePrimeExponentGenerator F hζ S₀ r ^ 6 ∈
      primePowerIdeal (sourceHilbertSeed F S₀) P.val n ↔
        n ≤ sourceElementExponents F S₀ u hu P + 6 * r P :=
    sourceFrequency_mem_primePower_iff F S₀ hζ u hu r P n
  exact ⟨(h _).mpr le_rfl, fun he => Nat.not_succ_le_self _ ((h _).mp he)⟩

end
end ArtinMatthews
