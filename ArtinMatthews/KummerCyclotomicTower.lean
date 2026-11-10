module

public import ArtinMatthews.KummerCyclotomicTowerBase
public import ArtinMatthews.KummerCyclotomicTowerAbelian
public import ArtinMatthews.KummerSplittingGaloisField
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
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


set_option backward.privateInPublic true
@[expose] public section

/-! Number fields, actual integral embeddings, and degree bounds for the
auxiliary cyclotomic compositum used in the zero-freeness descent. -/

noncomputable section
namespace ArtinMatthews
open scoped NumberField

/-- Ring-of-integers inclusions preserve the ambient field value. -/
theorem ringOfIntegers_inclusion_coe
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L : IntermediateField F E) (h : K ≤ L) (x : 𝓞 K) :
    ((NumberField.RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom x : L) : E) =
      ((x : K) : E) := rfl

/-- Actual field embeddings induce injective maps on the rings of integers. -/
theorem ringOfIntegers_mapRingHom_injective
    {F E : Type*} [Field F] [Field E] (f : F →+* E) :
    Function.Injective (NumberField.RingOfIntegers.mapRingHom f) := by
  intro x y h
  apply NumberField.RingOfIntegers.ext
  apply f.injective
  exact congrArg (fun z : 𝓞 E => (z : E)) h

instance twelfthCyclotomicField_numberField (q : ℕ) [NeZero q] :
    NumberField (twelfthCyclotomicField q) where

/-- The canonical inclusion on the actual rings of integers over F_q. -/
def twelfthKummerIntegersFromCyclotomic (q : ℕ) (a : ℤ) :
    𝓞 (twelfthCyclotomicField q) →+* 𝓞 (twelfthKummerField q a) :=
  algebraMap _ _

/-- The canonical inclusion on the actual rings of integers over K_q. -/
def twelfthKummerIntegersFromKummer (q : ℕ) (a : ℤ) [NeZero q] :
    𝓞 (primeKummerField q a) →+* 𝓞 (twelfthKummerField q a) :=
  NumberField.RingOfIntegers.mapRingHom
    (IntermediateField.inclusion (primeKummerField_le_twelfthKummerField q a)).toRingHom

@[simp] theorem twelfthKummerIntegersFromCyclotomic_coe (q : ℕ) (a : ℤ)
    (x : 𝓞 (twelfthCyclotomicField q)) :
    ((twelfthKummerIntegersFromCyclotomic q a x : twelfthKummerField q a) : ℂ) =
      ((x : twelfthCyclotomicField q) : ℂ) := rfl

@[simp] theorem twelfthKummerIntegersFromKummer_coe (q : ℕ) (a : ℤ) [NeZero q]
    (x : 𝓞 (primeKummerField q a)) :
    ((twelfthKummerIntegersFromKummer q a x : twelfthKummerField q a) : ℂ) =
      ((x : primeKummerField q a) : ℂ) :=
  ringOfIntegers_inclusion_coe (primeKummerField q a) (twelfthKummerField q a)
    (primeKummerField_le_twelfthKummerField q a) x

theorem twelfthKummerIntegersFromCyclotomic_injective (q : ℕ) (a : ℤ) :
    Function.Injective (twelfthKummerIntegersFromCyclotomic q a) := by
  intro x y h
  apply NumberField.RingOfIntegers.ext
  apply Subtype.ext
  exact congrArg (fun z : 𝓞 (twelfthKummerField q a) => ((z : twelfthKummerField q a) : ℂ)) h

theorem twelfthKummerIntegersFromKummer_injective (q : ℕ) (a : ℤ) [NeZero q] :
    Function.Injective (twelfthKummerIntegersFromKummer q a) :=
  ringOfIntegers_mapRingHom_injective _

theorem finrank_twelfthCyclotomicField (q : ℕ) [NeZero q] :
    Module.finrank ℚ (twelfthCyclotomicField q) = Nat.totient (12 * q) := by
  exact IsCyclotomicExtension.finrank (twelfthCyclotomicField q)
    (Polynomial.cyclotomic.irreducible_rat (Nat.mul_pos (by decide) (NeZero.pos q)))

/-- A uniform genuine absolute field-degree bound for the auxiliary compositum. -/
theorem twelfthKummerField_absolute_finrank_le (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    Module.finrank ℚ (twelfthKummerField q a) ≤ 12 * q ^ 2 := by
  have hf : Module.finrank ℚ (twelfthCyclotomicField q) ≤ 12 * q := by
    rw [finrank_twelfthCyclotomicField]
    exact Nat.totient_le _
  have hr : Module.finrank (twelfthCyclotomicField q) (twelfthKummerField q a) ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) (twelfthKummerField_relative_finrank_dvd q a)
  calc
    Module.finrank ℚ (twelfthKummerField q a) =
        Module.finrank ℚ (twelfthCyclotomicField q) *
          Module.finrank (twelfthCyclotomicField q) (twelfthKummerField q a) :=
      (Module.finrank_mul_finrank ℚ (twelfthCyclotomicField q) (twelfthKummerField q a)).symm
    _ ≤ (12 * q) * q := Nat.mul_le_mul hf hr
    _ = 12 * q ^ 2 := by ring

/-- The actual degree above K_q divides the auxiliary cyclotomic degree. -/
theorem twelfthKummerField_finrank_over_kummer_dvd_totient
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    Module.finrank (primeKummerField q a) (twelfthKummerField q a) ∣ Nat.totient (12 * q) := by
  have hc := Subgroup.card_dvd_of_injective (twelfthKummerRestriction q a)
    (twelfthKummerRestriction_injective q a)
  rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    finrank_twelfthCyclotomicField] at hc
  exact hc

end ArtinMatthews
