module

public import ArtinMatthews.KummerSplittingGaloisField
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
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

/-! The actual original Kummer field has no real places once q>2. -/
noncomputable section
namespace ArtinMatthews

/-- The original Kummer field contains the genuine cyclotomic subfield. -/
theorem primeKummerField_isTotallyComplex (q : ℕ) (a : ℤ) [NeZero q] (hq : 2 < q) :
    NumberField.IsTotallyComplex (primeKummerField q a) := by
  let : NumberField.IsTotallyComplex (primeCyclotomicField q) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (primeCyclotomicField q) hq
  let : Algebra (primeCyclotomicField q) (primeKummerField q a) :=
    inferInstanceAs (Algebra (primeCyclotomicField q)
      (IntermediateField.adjoin (primeCyclotomicField q) {primeRadicalRoot q a}))
  exact NumberField.isTotallyComplex_of_algebra (primeCyclotomicField q) (primeKummerField q a)

theorem primeKummerField_nrRealPlaces (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] (hq : 2 < q) :
    NumberField.InfinitePlace.nrRealPlaces (primeKummerField q a) = 0 := by
  let := primeKummerField_isTotallyComplex q a hq
  exact NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (primeKummerField q a)

end ArtinMatthews
