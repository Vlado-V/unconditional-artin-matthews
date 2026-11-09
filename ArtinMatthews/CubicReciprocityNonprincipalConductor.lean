module

public import ArtinMatthews.CubicReciprocityNonprincipalModel


set_option backward.privateInPublic true
@[expose] public section

/-! The explicit finite modulus used by the cubic numerator character. -/

noncomputable section

namespace ArtinMatthews

open OAI.SevenEighths

local notation "EO" => HeckeFamily.O

/-- The literal modulus of the transported cubic numerator character. -/
def cubicNumeratorHeckeModulus (A : ℤ) : Ideal EO := Ideal.span {9 * (A : EO)}

theorem cubicNumeratorHeckeModulus_ne_bot {A : ℤ} (hA : A ≠ 0) :
    cubicNumeratorHeckeModulus A ≠ ⊥ := by
  apply Ideal.span_singleton_eq_bot.not.mpr
  exact mul_ne_zero (by norm_num) (by exact_mod_cast hA)

/-- The residue modulus has norm `81 |A|²`; no unknown conductor constant
is introduced by changing the Eisenstein-ring model. -/
theorem cubicNumeratorHeckeModulus_absNorm (A : ℤ) :
    (cubicNumeratorHeckeModulus A).absNorm = 81 * A.natAbs ^ 2 := by
  have hrank : Module.finrank ℤ EO = 2 := by
    rw [NumberField.RingOfIntegers.rank HeckeFamily.K,
      IsCyclotomicExtension.Rat.finrank 3 HeckeFamily.K]
    decide
  rw [cubicNumeratorHeckeModulus, Ideal.absNorm_span_singleton]
  rw [show (9 : EO) * (A : EO) = algebraMap ℤ EO (9 * A) by simp]
  rw [Algebra.norm_algebraMap, hrank]
  simp [Int.natAbs_mul, mul_pow]

end ArtinMatthews
