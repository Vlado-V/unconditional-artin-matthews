module

public import ArtinMatthews.SourceReflectionDeepUnits
public import ArtinMatthews.HeckeExtension.SourceSupportedRay
public import ArtinMatthews.PrincipalAngularCorrection


set_option backward.privateInPublic true
@[expose] public section

/-! The literal angular and Gauss moduli, and the target modulus allowed
by the source cutoff, are supported in the same retained finite set. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField IsDedekindDomain AllowedGenerators
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "S" => sourceHilbertSet F S₀
local notation "A" => sixthKummerFixedIdeal S
local notation "three" => (Ideal.span {(3 : 𝓞 F)} : Ideal (𝓞 F))

def sourceReflectionAngularModulus : Ideal (𝓞 F) := three * A

theorem sourceReflectionAngularModulus_ne_bot : sourceReflectionAngularModulus F S₀ ≠ ⊥ := by
  have h3 : three ≠ ⊥ := by rw [ne_eq, Ideal.span_singleton_eq_bot]; norm_num
  exact mul_ne_zero h3 (sixthKummerFixedIdeal_ne_zero S)

theorem sourceReflectionAngularModulus_support :
    (integralIdealFiniteModulus (sourceReflectionAngularModulus F S₀)
      (sourceReflectionAngularModulus_ne_bot F S₀)).support = S := by
  ext P
  rw [integralIdealFiniteModulus_mem_support]
  have hA : P.asIdeal ∣ A ↔ P ∈ S := by
    rw [← integralIdealFiniteModulus_mem_support A (sixthKummerFixedIdeal_ne_zero S),
      sixthKummerFixedIdeal_support F S]
  constructor
  · intro hP
    rcases P.prime.dvd_mul.mp hP with h | h
    · by_contra hPS
      have h3 : (3:𝓞 F) ∈ P.asIdeal := Ideal.dvd_span_singleton.mp h
      apply source_exterior_six_not_mem F S₀ P hPS
      simpa only [show (2:𝓞 F) * 3 = 6 by norm_num] using P.asIdeal.mul_mem_left 2 h3
    · exact hA.mp h
  · intro hP
    exact dvd_mul_of_dvd_right (hA.mpr hP) three

theorem sourceReflectionGaussModulus_support :
    (integralIdealFiniteModulus (A * A)
      (mul_ne_zero (sixthKummerFixedIdeal_ne_zero S) (sixthKummerFixedIdeal_ne_zero S))).support = S := by
  ext P
  rw [integralIdealFiniteModulus_mem_support, P.prime.dvd_mul, or_self,
    ← integralIdealFiniteModulus_mem_support A (sixthKummerFixedIdeal_ne_zero S),
    sixthKummerFixedIdeal_support F S]

theorem sourceReflectionTargetModulus_support {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff F J ⊆ S) :
    (integralIdealFiniteModulus J hJ).support ⊆ S := by
  intro P hP
  by_contra hPS
  have hc := principalAngularCutoff_coprime hJ P (fun h => hPS (hcut h))
  have hd := (integralIdealFiniteModulus_mem_support J hJ P).mp hP
  exact P.prime.not_isUnit (hc.isUnit_of_dvd' dvd_rfl hd)

theorem sourcePrimeExponentIdeal_coprime_of_modulusSupport {J : Ideal (𝓞 F)} (hJ : J ≠ ⊥)
    (hJSupp : (integralIdealFiniteModulus J hJ).support ⊆ S) (e : SourcePrimeExponents F S₀) :
    IsCoprime (sourcePrimeExponentIdeal F S₀ e) J := by
  apply IsCoprime.prod_left
  intro P _
  have hc : IsCoprime P.val.asIdeal J := by
    apply principalAngular_prime_coprime_of_not_le P.val J
    intro hle
    exact P.property (hJSupp ((integralIdealFiniteModulus_mem_support J hJ P.val).mpr
      (Ideal.dvd_iff_le.mpr hle)))
  exact hc.pow_left

end
end ArtinMatthews.VaryingKummerAnalytic
