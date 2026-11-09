module

public import ArtinMatthews.KummerSplittingDegree
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.AlgebraTower
public import Mathlib


set_option backward.privateInPublic true
@[expose] public section

/-! Actual integral power bases for the varying-prime Kummer fields. -/

noncomputable section
namespace ArtinMatthews

/-- The chosen roots are integral even at the harmless total-definition value `q=0`. -/
theorem primeCyclotomicRoot_isIntegral (q : ℕ) :
    IsIntegral ℤ (primeCyclotomicRoot q) := by
  by_cases hq : q = 0
  · subst q
    simpa [primeCyclotomicRoot] using (isIntegral_one : IsIntegral ℤ (1 : ℂ))
  · apply IsIntegral.of_pow (Nat.pos_of_ne_zero hq)
    rw [primeCyclotomicRoot_pow (Nat.pos_of_ne_zero hq)]
    exact isIntegral_one

theorem primeRadicalRoot_isIntegral (q : ℕ) (a : ℤ) :
    IsIntegral ℤ (primeRadicalRoot q a) := by
  by_cases hq : q = 0
  · subst q
    simpa [primeRadicalRoot] using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · apply IsIntegral.of_pow (Nat.pos_of_ne_zero hq)
    rw [primeRadicalRoot_pow (Nat.pos_of_ne_zero hq) a]
    exact isIntegral_algebraMap

/-- The same actual field before restricting its scalar tower to `ℚ`. -/
def primeKummerTowerField (q : ℕ) (a : ℤ) :
    IntermediateField (primeCyclotomicField q) ℂ :=
  IntermediateField.adjoin (primeCyclotomicField q) {primeRadicalRoot q a}

/-- Scalar restriction does not change the underlying field. -/
def primeKummerTowerRingEquiv (q : ℕ) (a : ℤ) :
    primeKummerTowerField q a ≃+* primeKummerField q a := RingEquiv.refl _

instance primeCyclotomicField_numberField (q : ℕ) : NumberField (primeCyclotomicField q) := by
  let : FiniteDimensional ℚ (primeCyclotomicField q) :=
    IntermediateField.adjoin.finiteDimensional ((primeCyclotomicRoot_isIntegral q).tower_top)
  exact NumberField.of_module_finite ℚ (primeCyclotomicField q)

instance primeKummerTowerField_numberField (q : ℕ) (a : ℤ) :
    NumberField (primeKummerTowerField q a) := by
  let : FiniteDimensional (primeCyclotomicField q) (primeKummerTowerField q a) :=
    IntermediateField.adjoin.finiteDimensional ((primeRadicalRoot_isIntegral q a).tower_top)
  exact NumberField.of_module_finite (primeCyclotomicField q) (primeKummerTowerField q a)

instance primeKummerField_numberField (q : ℕ) (a : ℤ) : NumberField (primeKummerField q a) :=
  NumberField.of_ringEquiv _ _ (primeKummerTowerRingEquiv q a)

def primeCyclotomicPowerBasis (q : ℕ) : PowerBasis ℚ (primeCyclotomicField q) :=
  IntermediateField.adjoin.powerBasis ((primeCyclotomicRoot_isIntegral q).tower_top)

def primeKummerRelativePowerBasis (q : ℕ) (a : ℤ) :
    PowerBasis (primeCyclotomicField q) (primeKummerTowerField q a) :=
  IntermediateField.adjoin.powerBasis ((primeRadicalRoot_isIntegral q a).tower_top)

end ArtinMatthews
