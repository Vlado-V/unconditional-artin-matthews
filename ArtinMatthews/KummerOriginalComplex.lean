module

public import ArtinMatthews.KummerCyclotomicTower
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings


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
