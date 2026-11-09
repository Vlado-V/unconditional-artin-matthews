module

public import ArtinMatthews.SourceReflectionTameSign
public import OAI.NumberTheory.DirichletL.GaussSum.FiniteTranslations


set_option backward.privateInPublic true
@[expose] public section

/-! Finite Fourier coefficients for the actual residue character and
standard additive phase. Character powers are taken in the monoid of
zero-extended multiplicative characters, including the zeroth power. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open SIntegerFourier
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "ψ₀" => sourceJacquetActualPositivePhase K hζ S₀ P
local notation "Γ₀" => sourceJacquetActualGauss K hζ S₀ P
local notation "Q₀" => (Ideal.absNorm P.val.asIdeal : ℂ)
local notation "sQ" => (Real.sqrt (Ideal.absNorm P.val.asIdeal : ℝ) : ℂ)

local instance reflectionResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance reflectionResidueFinite : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance reflectionResidueFintype : Fintype R := Fintype.ofFinite _

private theorem residue_card : Fintype.card R = Ideal.absNorm P.val.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

private theorem residue_card_units : (Fintype.card Rˣ : ℂ) = Q₀ - 1 := by
  apply eq_sub_iff_add_eq.mpr
  have hc := Fintype.card_eq_card_units_add_one R
  rw [residue_card K S₀ P] at hc
  exact_mod_cast hc.symm

private theorem residue_norm_ne_zero : Q₀ ≠ 0 :=
  Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot)

private theorem residue_sqrt_sq : sQ * sQ = Q₀ := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

private theorem residue_sqrt_ne_zero : sQ ≠ 0 := by
  intro h
  apply residue_norm_ne_zero K S₀ P
  rw [← residue_sqrt_sq K S₀ P, h, mul_zero]

private theorem residue_character_pow_ne_one (j : ℕ) (hj : ¬ 6 ∣ j) : χ₀ ^ j ≠ 1 := by
  intro he
  have hd := orderOf_dvd_iff_pow_eq_one.mpr he
  rw [sourceJacquetActualCharacter_order] at hd
  exact hj hd

private theorem residue_character_pow_six : χ₀ ^ (6 : ℕ) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, sourceJacquetActualCharacter_order]

theorem sourceReflectionTameResiduePhase_ne_one
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) : ψ₀ ≠ 1 := by
  intro he
  have he' := congrArg Inv.inv he
  rw [sourceJacquetActualPositivePhase, inv_inv, inv_one] at he'
  exact residueSourcePhase_ne_one (sourceHilbertSeed K S₀) P.val P.property
    (sourceAllowedPrimeGenerator K hζ S₀ P) (sourceAllowedPrimeGenerator_ideal K hζ S₀ P)
    (fun hp => P.property (hS (Finset.mem_union_left _ hp))) he'

theorem sourceReflectionTameResiduePhase_primitive
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) : (ψ₀).IsPrimitive := by
  intro a ha hs
  exact sourceReflectionTameResiduePhase_ne_one K hζ S₀ P hS
    ((AddChar.mulShift_unit_eq_one_iff ψ₀ (isUnit_iff_ne_zero.mpr ha)).mp hs)

def sourceReflectionTameFourierCoefficient (j : Fin 6) (h : R) : ℂ :=
  OAI.CubicEisenstein.finiteAdditiveFourierCoeff ψ₀ (⇑(χ₀ ^ j.val : MulChar R ℂ)) h

local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P

theorem sourceReflectionTameFourier_inversion
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (j : Fin 6) (x : R) :
    (∑ h : R, C₀ j h * ψ₀ (h * x)) = (χ₀ ^ j.val : MulChar R ℂ) x :=
  OAI.CubicEisenstein.finiteAdditiveFourier_inversion ψ₀
    (sourceReflectionTameResiduePhase_primitive K hζ S₀ P hS) (⇑(χ₀ ^ j.val : MulChar R ℂ)) x

theorem sourceReflectionTameFourierCoefficient_zero (j : Fin 6) :
    C₀ j 0 = if j = 0 then 1 - Q₀⁻¹ else 0 := by
  unfold sourceReflectionTameFourierCoefficient OAI.CubicEisenstein.finiteAdditiveFourierCoeff
  simp only [neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one, residue_card K S₀ P]
  by_cases hj : j = 0
  · subst j
    rw [ite_eq_left rfl, Fin.val_zero, pow_zero, MulChar.sum_one_eq_card_units, residue_card_units K S₀ P]
    field_simp [residue_norm_ne_zero K S₀ P]
  · have hj' : ¬ 6 ∣ j.val := by
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext h)
      omega
    rw [ite_eq_right hj, MulChar.sum_eq_zero_of_ne_one (residue_character_pow_ne_one K hζ S₀ P _ hj'), zero_div]

private theorem gauss_positive (j : ℕ) :
    gaussSum (χ₀ ^ j) ψ₀ = Γ₀ j * sQ := by
  rw [sourceJacquetActualGauss_positive, tsum_fintype, ← gaussSum,
    div_mul_cancel₀ _ (residue_sqrt_ne_zero K S₀ P)]

private theorem gauss_negative (j : ℕ) :
    gaussSum (χ₀ ^ j) ((ψ₀).mulShift (-1)) = Γ₀ j * sQ := by
  let φ := residueSourcePhase (sourceHilbertSeed K S₀) P.val P.property
    (sourceAllowedPrimeGenerator K hζ S₀ P) (sourceAllowedPrimeGenerator_ideal K hζ S₀ P)
  have hphase : (ψ₀).mulShift (-1) = φ := by
    ext x
    rw [AddChar.mulShift_apply, neg_one_mul, sourceJacquetActualPositivePhase, AddChar.inv_apply, neg_neg]
  rw [hphase]
  change gaussSum (χ₀ ^ j) φ = (∑' x : R, (χ₀ ^ j : MulChar R ℂ) x * φ x) / sQ * sQ
  rw [tsum_fintype, ← gaussSum, div_mul_cancel₀ _ (residue_sqrt_ne_zero K S₀ P)]

def sourceReflectionTameFourierHead (j : Fin 6) : ℂ :=
  if j = 0 then -Q₀⁻¹ else Γ₀ j.val / sQ

local notation "H₀" => sourceReflectionTameFourierHead K hζ S₀ P

theorem sourceReflectionTameFourierCoefficient_unit
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (j : Fin 6) (h : Rˣ) :
    C₀ j h = H₀ j * ((χ₀ ^ j.val)⁻¹) h := by
  unfold sourceReflectionTameFourierCoefficient OAI.CubicEisenstein.finiteAdditiveFourierCoeff
    sourceReflectionTameFourierHead
  rw [residue_card K S₀ P]
  by_cases hj : j = 0
  · subst j
    rw [ite_eq_left (rfl : (0 : Fin 6) = 0)]
    simp only [Fin.val_zero, pow_zero, inv_one, MulChar.one_apply_coe, mul_one, neg_mul]
    rw [OAI.ShortDraftLocal.trivial_fourier_coefficient ψ₀
      (sourceReflectionTameResiduePhase_ne_one K hζ S₀ P hS) (h : R),
      ite_eq_right (Units.ne_zero h), div_eq_mul_inv, neg_one_mul]
  · have hj' : ¬ 6 ∣ j.val := by
      have hj0 : j.val ≠ 0 := fun he => hj (Fin.ext he)
      omega
    simp only [neg_mul]
    rw [OAI.ShortDraftLocal.nontrivial_fourier_coefficient _ ψ₀
      (residue_character_pow_ne_one K hζ S₀ P _ hj'), gauss_negative K hζ S₀ P, ite_eq_right hj,
      ← residue_sqrt_sq K S₀ P]
    field_simp [residue_sqrt_ne_zero K S₀ P]

def sourceReflectionTameActiveFourier (j : Fin 6) (x : R) : ℂ :=
  ∑ h : Rˣ, C₀ j h * ((χ₀⁻¹) ^ (2 : ℕ)) h * ψ₀ (x * ((h⁻¹ : Rˣ) : R))

local notation "A₀" => sourceReflectionTameActiveFourier K hζ S₀ P

theorem sourceReflectionTameActiveFourier_eq_gauss
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (j : Fin 6) (x : R) :
    A₀ j x = H₀ j * gaussSum (χ₀ ^ (j.val + 2)) ((ψ₀).mulShift x) := by
  rw [sourceReflectionTameActiveFourier, ← OAI.ShortDraftLocal.general_inversion_gauss, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [sourceReflectionTameFourierCoefficient_unit K hζ S₀ P hS, MulChar.mul_apply]
  ring

/-- Active primes have the exact cubic, Ramanujan, and sextic Gauss branches. -/
theorem sourceReflectionTameActiveFourier_eq
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (j : Fin 6) (x : R) :
    A₀ j x =
      if j = 0 then -(Γ₀ 2 / sQ) * ((χ₀ ^ (2 : ℕ))⁻¹) x
      else if j = 4 then (Γ₀ 4 / sQ) * (if x = 0 then Q₀ - 1 else -1)
      else Γ₀ j.val * Γ₀ (j.val + 2) * ((χ₀ ^ (j.val + 2))⁻¹) x := by
  rw [sourceReflectionTameActiveFourier_eq_gauss K hζ S₀ P hS,
    sourceReflectionTameFourierHead]
  by_cases hj0 : j = 0
  · subst j
    simp only [Fin.val_zero, zero_add, eq_self, ite_true]
    rw [OAI.ShortDraftLocal.gaussSum_mulShift_any _ ψ₀
        (residue_character_pow_ne_one K hζ S₀ P 2 (by decide)),
      gauss_positive K hζ S₀ P, ← residue_sqrt_sq K S₀ P]
    field_simp [residue_sqrt_ne_zero K S₀ P] <;> ring
  · simp only [ite_eq_right hj0]
    by_cases hj4 : j = 4
    · subst j
      rw [ite_eq_left rfl]
      change (Γ₀ 4 / sQ) * gaussSum (χ₀ ^ (6 : ℕ)) ((ψ₀).mulShift x) = _
      rw [residue_character_pow_six K hζ S₀ P, OAI.ShortDraftLocal.gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
      rw [OAI.ShortDraftLocal.additive_unit_sum ψ₀
        (sourceReflectionTameResiduePhase_ne_one K hζ S₀ P hS), residue_card_units K S₀ P]
    · have hj' : ¬ 6 ∣ j.val + 2 := by
        have hj4' : j.val ≠ 4 := fun he => hj4 (Fin.ext he)
        have hjlt := j.isLt
        omega
      rw [ite_eq_right hj4, OAI.ShortDraftLocal.gaussSum_mulShift_any _ ψ₀
        (residue_character_pow_ne_one K hζ S₀ P _ hj'), gauss_positive K hζ S₀ P]
      field_simp [residue_sqrt_ne_zero K S₀ P] <;> ring

theorem sourceReflectionTameActiveFourier_one
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (x : R) :
    A₀ 1 x = Γ₀ 1 * Γ₀ 3 * (χ₀ ^ (3 : ℕ)) x := by
  rw [sourceReflectionTameActiveFourier_eq K hζ S₀ P hS,
    ite_eq_right (by decide : (1 : Fin 6) ≠ 0), ite_eq_right (by decide : (1 : Fin 6) ≠ 4)]
  exact congrArg (fun c : MulChar R ℂ => Γ₀ 1 * Γ₀ 3 * c x)
    (OAI.ShortDraftLocal.sextic_character_quadratic χ₀ (residue_character_pow_six K hζ S₀ P))

end
end ArtinMatthews
