module

public import ArtinMatthews.ArtinFrobeniusPrimeAvoidance
public import ArtinMatthews.IdealRayCoefficientSeparation


set_option backward.privateInPublic true
@[expose] public section

/-! Primitive coefficient equality separates actual Galois characters
using only prime values outside both old moduli and an additional finite
exclusion. Conductor divisibility keeps both coefficient masks nonzero. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GaloisIdealCharacter
open scoped NumberField nonZeroDivisors Classical
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

theorem galoisCharacter_eq_of_primitive_coefficients
    (M₁ M₂ C : Ideal (𝓞 K)) (hM₁ : M₁ ≠ ⊥) (hM₂ : M₂ ≠ ⊥) (hC : C ≠ ⊥)
    {f g : Ideal (𝓞 K)} (ψ : EvenIdealRayCharacter K f) (φ : EvenIdealRayCharacter K g)
    (hf : M₁ ≤ f) (hg : M₂ ≤ g) (χ θ : Gal(L/K) →* ℂˣ)
    (hψ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₁ → IsCoprime v.asIdeal C →
      ψ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot)=χ (primeFrobenius K L v))
    (hφ : ∀ v : HeightOneSpectrum (𝓞 K), IsCoprime v.asIdeal M₂ → IsCoprime v.asIdeal C →
      φ.idealHom (integralIdealFractionalUnit v.asIdeal v.ne_bot)=θ (primeFrobenius K L v))
    (he : ψ.coefficient=φ.coefficient) : χ=θ := by
  by_contra hne
  obtain ⟨v,hv,hsep⟩ := exists_prime_separating_frobenius_avoiding
    (M₁*M₂*C) (mul_ne_zero (mul_ne_zero hM₁ hM₂) hC) χ θ hne
  have hc : (IsCoprime v.asIdeal M₁ ∧ IsCoprime v.asIdeal M₂) ∧ IsCoprime v.asIdeal C := by
    simpa only [IsCoprime.mul_right_iff] using hv
  have hcf : IsCoprime v.asIdeal f :=
    hc.1.1.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hf)
  have hcg : IsCoprime v.asIdeal g :=
    hc.1.2.of_isCoprime_of_dvd_right (Ideal.dvd_iff_le.mpr hg)
  have hval := EvenIdealRayCharacter.idealHom_eq_of_coefficient_eq_of_coprime
    ψ φ he v.asIdeal v.ne_bot hcf hcg
  apply hsep
  exact (hψ v hc.1.1 hc.2).symm.trans (hval.trans (hφ v hc.1.2 hc.2))

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
