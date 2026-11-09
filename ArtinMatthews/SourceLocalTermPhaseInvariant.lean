module

public import ArtinMatthews.SourceStrippedPhaseComparison
public import ArtinMatthews.SourceThetaPhaseComparison
public import ArtinMatthews.ProbeIdealSourceWeight


set_option backward.privateInPublic true
@[expose] public section

/-! Exact phase cancellation in each source term, even at primes that
divide the frequency representative. This is the bridge from the literal
standard-phase calF to the existing analytic local coefficient series. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

theorem sourcePhaseProduct_cancel (b : ℂ) (hb : b ^ 6 = 1) (e l : ℕ) :
    let t := e + 3 * l
    ((b⁻¹ ^ 2) ^ e) * (b⁻¹ ^ t) * ((b ^ 3) ^ t) = 1 := by
  let t := e + 3 * l
  have hb0 : b ≠ 0 := by
    intro he
    simp only [he, zero_pow (by decide : (6 : ℕ) ≠ 0), zero_ne_one] at hb
  have ht : 3 * t = 2 * e + t + 6 * l := by dsimp only [t]; omega
  have h₆ : b ^ (6 * l) = 1 := by rw [pow_mul, hb, one_pow]
  change (b⁻¹ ^ 2) ^ e * b⁻¹ ^ t * (b ^ 3) ^ t = 1
  rw [← pow_mul b⁻¹ 2 e, ← pow_add, inv_pow, ← pow_mul b 3 t, ht, pow_add b (2 * e + t) (6 * l), h₆, mul_one,
    inv_mul_cancel₀ (pow_ne_zero _ hb0)]

theorem sourceUnit_zpow_sub (b : ℂˣ) (k t : ℕ) :
    ((b ^ ((k : ℤ) - t) : ℂˣ) : ℂ) = (b : ℂ) ^ k * ((b : ℂ)⁻¹) ^ t := by
  rw [zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul,
    Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, inv_pow]

theorem sourceLocalNormPower (Q : ℂ) (hQ : Q ≠ 0) (ξ w z : ℂ) (e l k m : ℕ) :
    (Q ^ (-(1 / 2 : ℂ) - ξ)) ^ e * (Q ^ (-1 - 3 * ξ)) ^ l *
      (Q ^ (-w)) ^ k * (Q ^ (-(6 : ℂ) * z)) ^ m =
        Q ^ (-((e : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z)) := by
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ, ← Complex.cpow_add _ _ hQ]
  congr 1
  ring

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (P : SourceExteriorPrime F S₀)

local notation "χ" => reflectionPrimeCharacters F hζ S₀ P
local notation "Θ" => reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1)
local notation "Θ₀" => probeIdealGaussLocalVartheta F P.val χ (η.allCoefficient P.val.asIdeal)
local notation "Γ" => reflectionNormalizedPrimeGamma F hζ S₀ P
local notation "Γ₀" => probeIdealGaussGamma F P.val χ 2
local notation "C" => sourcePrimeStrippedCoefficient F hζ S₀ P
local notation "C₀" => probeIdealLocalCoefficient F P.val χ

theorem sourcePrimeCoefficientPhase_cancel (e l k J : ℕ) :
    let t := e + 3 * l
    Γ ^ e * C t k J * Θ ^ t = Γ₀ ^ e * C₀ t k J * Θ₀ ^ t := by
  obtain ⟨a, ha⟩ := sourcePrimeResiduePhase_exists_mulShift F hζ S₀ P hS
  let t := e + 3 * l
  change Γ ^ e * C t k J * Θ ^ t = Γ₀ ^ e * C₀ t k J * Θ₀ ^ t
  have hΓ := congrArg (fun g : ℂ => g ^ e) (sourceNormalizedPrimeGamma_mulShift F hζ S₀ P a ha)
  have hC := sourcePrimeStrippedCoefficient_mulShift F hζ S₀ hS P a ha t k J
  have hΘ := congrArg (fun g : ℂ => g ^ t) (sourcePrimeTheta_mulShift F hζ S₀ hS η P a ha)
  calc
    _ = ((χ a)⁻¹ ^ 2 * Γ₀) ^ e * ((χ a)⁻¹ ^ t * C₀ t k J) *
        ((χ a) ^ 3 * Θ₀) ^ t := congrArg₂ (· * ·) (congrArg₂ (· * ·) hΓ hC) hΘ
    _ = ((χ a)⁻¹ ^ 2) ^ e * (χ a)⁻¹ ^ t * ((χ a) ^ 3) ^ t *
        (Γ₀ ^ e * C₀ t k J * Θ₀ ^ t) := by
      simp only [mul_pow]
      ring
    _ = _ := by
      rw [sourcePhaseProduct_cancel _ (sourcePrimeCharacter_unit_pow_six F hζ S₀ P a) e l,
        one_mul]

theorem sourceLocalEulerTerm_eq_ideal (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
    (i : SourceLocalChoice) :
    sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P i =
      probeIdealSourceTerm F P.val χ (sourceElementExponents F S₀ u hu P)
        Γ₀ Θ₀ (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ)
        ξ w z i.1 i.2.1 i.2.2.1 i.2.2.2 := by
  rcases i with ⟨e, l, k, m⟩
  let t := e.val + 3 * l
  let J := sourceElementExponents F S₀ u hu P + 6 * m
  let θ := sourceResidualCharacterUnit F hζ S₀ u hu P
  let Q : ℂ := Ideal.absNorm P.val.asIdeal
  let N := (Q ^ (-(1 / 2 : ℂ) - ξ)) ^ e.val * (Q ^ (-1 - 3 * ξ)) ^ l *
    (Q ^ (-w)) ^ k * (Q ^ (-(6 : ℂ) * z)) ^ m
  have hQ : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot
  have hN := sourceLocalNormPower Q hQ ξ w z e.val l k m
  have hScale : Γ ^ e.val * C t k J * Θ ^ t = Γ₀ ^ e.val * C₀ t k J * Θ₀ ^ t :=
    sourcePrimeCoefficientPhase_cancel F hζ S₀ hS η P e.val l k J
  change Γ ^ e.val * (((θ ^ ((k : ℤ) - t) : ℂˣ) : ℂ)) * C t k J * Θ ^ t *
    (Q ^ (-(1 / 2 : ℂ) - ξ)) ^ e.val * (Q ^ (-1 - 3 * ξ)) ^ l *
      (Q ^ (-w)) ^ k * (Q ^ (-(6 : ℂ) * z)) ^ m = _
  calc
    _ = (Γ ^ e.val * C t k J * Θ ^ t) * (((θ ^ ((k : ℤ) - t) : ℂˣ) : ℂ)) * N := by
      dsimp only [N]
      ac_rfl
    _ = _ := by
      rw [hScale, sourceUnit_zpow_sub, show N = _ from hN]
      unfold probeIdealSourceTerm
      change _ = C₀ t k J * Γ₀ ^ e.val * Θ₀ ^ t *
        (θ : ℂ) ^ k * ((θ : ℂ)⁻¹) ^ t *
        Q ^ (-((e.val : ℂ) * (1 / 2 + ξ) + (l : ℂ) * (1 + 3 * ξ) + (k : ℂ) * w + (6 * m : ℂ) * z))
      dsimp only [t]
      ac_rfl

end
end ArtinMatthews.SourceEulerAssembly
