module

public import ArtinMatthews.KummerCyclotomicTower
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings


set_option backward.privateInPublic true
@[expose] public section

/-! The actual auxiliary cyclotomic tower has no real places.  Thus the
infinite sign conditions in its ray conductor impose no additional restriction. -/
namespace ArtinMatthews
open NumberField
noncomputable section

instance twelfthCyclotomicField_isTotallyComplex (q : ℕ) [NeZero q] :
    NumberField.IsTotallyComplex (twelfthCyclotomicField q) := by
  have hn : 2 < 12*q := by have hq := NeZero.pos q; omega
  exact IsCyclotomicExtension.Rat.isTotallyComplex (twelfthCyclotomicField q) hn

instance twelfthKummerField_isTotallyComplex (q : ℕ) (a : ℤ) [NeZero q] :
    NumberField.IsTotallyComplex (twelfthKummerField q a) :=
  NumberField.isTotallyComplex_of_algebra (twelfthCyclotomicField q) (twelfthKummerField q a)

theorem twelfthCyclotomicField_nrRealPlaces (q : ℕ) [NeZero q] :
    NumberField.InfinitePlace.nrRealPlaces (twelfthCyclotomicField q) = 0 :=
  NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (twelfthCyclotomicField q)

theorem twelfthKummerField_nrRealPlaces (q : ℕ) (a : ℤ) [NeZero q] [NeZero a] :
    NumberField.InfinitePlace.nrRealPlaces (twelfthKummerField q a) = 0 :=
  NumberField.IsTotallyComplex.nrRealPlaces_eq_zero (twelfthKummerField q a)

theorem twelfthCyclotomicField_realPlace_isEmpty (q : ℕ) [NeZero q] :
    IsEmpty {v : NumberField.InfinitePlace (twelfthCyclotomicField q) // v.IsReal} := by
  refine ⟨fun v => ?_⟩
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (NumberField.IsTotallyComplex.isComplex v.1)) v.2

end
end ArtinMatthews
