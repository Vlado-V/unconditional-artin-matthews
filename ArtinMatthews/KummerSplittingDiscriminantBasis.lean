module

public import ArtinMatthews.KummerSplittingDegree
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


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
