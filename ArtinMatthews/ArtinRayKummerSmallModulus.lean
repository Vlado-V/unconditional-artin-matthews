module

public import ArtinMatthews.ArtinRaySmallModulus
public import ArtinMatthews.KummerOriginalComplex


set_option backward.privateInPublic true
@[expose] public section

/-! Actual ray families for both preserved Kummer towers, at the explicit
discriminant-times-relative-degree-square modulus. -/
noncomputable section
open scoped NumberField Classical
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open GaloisIdealCharacter

theorem twelfthKummer_cyclotomic_small_ray_family
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (haq : a.natAbs ≤ q) :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      Real.log (N : ℝ) ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) ∧
      ∃ ψ : (Gal(twelfthKummerField q a/twelfthCyclotomicField q) →* ℂˣ) →
          EvenRayCharacter (twelfthCyclotomicField q) N,
        (∀ χ, (ψ χ).idealHom =
          idealHom (twelfthCyclotomicField q) (twelfthKummerField q a) χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  refine ⟨discriminantDegreeModulus (twelfthCyclotomicField q) (twelfthKummerField q a),
    discriminantDegreeModulus_pos _ _, discr_dvd_discriminantDegreeModulus _ _,
    twelfthKummer_cyclotomic_discriminantDegreeModulus_log_le q a haq,
    discriminantDegreeRayCharacter, ?_, ?_⟩
  · intro χ
    rfl
  · exact discriminantDegreeRayCharacter_isNonprincipal

theorem twelfthKummer_original_small_ray_family
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (hq : 2 < q) (haq : a.natAbs ≤ q) :
    ∃ N : ℕ, 0 < N ∧ (NumberField.discr (twelfthKummerField q a)).natAbs ∣ N ∧
      Real.log (N : ℝ) ≤ (72 * (q : ℝ)^2 + 2) * Real.log (12 * q) ∧
      ∃ ψ : (Gal(twelfthKummerField q a/primeKummerField q a) →* ℂˣ) →
          EvenRayCharacter (primeKummerField q a) N,
        (∀ χ, (ψ χ).idealHom =
          idealHom (primeKummerField q a) (twelfthKummerField q a) χ) ∧
        ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal := by
  let := primeKummerField_isTotallyComplex q a hq
  refine ⟨discriminantDegreeModulus (primeKummerField q a) (twelfthKummerField q a),
    discriminantDegreeModulus_pos _ _, discr_dvd_discriminantDegreeModulus _ _,
    twelfthKummer_original_discriminantDegreeModulus_log_le q a haq,
    discriminantDegreeRayCharacter, ?_, ?_⟩
  · intro χ
    rfl
  · exact discriminantDegreeRayCharacter_isNonprincipal

end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
end
