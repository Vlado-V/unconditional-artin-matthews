module

public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.ArtinRayNonprincipal


set_option backward.privateInPublic true
@[expose] public section

/-! The exact sign and nonprincipality of the genuine ideal Artin character. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField IsDedekindDomain
open GlobalClassFieldTheory GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField Classical
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
variable [NumberField.IsTotallyComplex K]

theorem abelianNormConductorRayCharacter_pow
    (χ : Gal(L/K) →* ℂˣ) (n : ℕ) (hχ : ∀ σ, χ σ ^ n = 1) (I : FractionalIdealGroup K) :
    (abelianNormConductorRayCharacter K L χ).idealHom I ^ n = 1 := by
  rw [abelianNormConductorRayCharacter_idealHom]
  change (∏ᶠ P : HeightOneSpectrum (𝓞 K),
    χ (GaloisIdealCharacter.primeFrobenius K L P) ^ FractionalIdeal.count K P I.val) ^ n = 1
  rw [finprod_pow (GaloisIdealCharacter.finite_factor_support K L χ I)]
  have hp (P : HeightOneSpectrum (𝓞 K)) :
      (χ (GaloisIdealCharacter.primeFrobenius K L P) ^ FractionalIdeal.count K P I.val) ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hχ, one_zpow]
  simp only [hp, finprod_one]

theorem abelianNormConductorRayCharacter_isNonprincipal
    (χ : Gal(L/K) →* ℂˣ) (hχ : χ ≠ 1) :
    (abelianNormConductorRayCharacter K L χ).IsNonprincipal := by
  let M := abelianNormConductorIdeal K L
  let hM := abelianNormConductorIdeal_ne_bot K L
  obtain ⟨v, hv, hvalue⟩ := exists_prime_frobenius_value_ne_one (integralIdealRayModulus M hM)
    (integralIdeal_congruence_le_norm_of_local M hM (abelianNormConductorIdeal_localNorm K L))
    (abelianNormConductorIdeal_unramified K L) χ hχ
  have hnd : ¬ v.asIdeal ∣ M := mt (integralIdealFiniteModulus_mem_support M hM v).mpr hv
  have hc : IsCoprime v.asIdeal M := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    obtain ⟨a, ha, han⟩ := Set.not_subset.mp (fun h => hnd (Ideal.dvd_iff_le.mpr h))
    exact (Ideal.isMaximal_iff.mp inferInstance).2 _ a le_sup_left han (Submodule.mem_sup_right ha)
  refine ⟨v.asIdeal, v.ne_bot, hc, ?_⟩
  rw [abelianNormConductorRayCharacter_idealHom, GaloisIdealCharacter.idealHom_prime]
  exact hvalue

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
