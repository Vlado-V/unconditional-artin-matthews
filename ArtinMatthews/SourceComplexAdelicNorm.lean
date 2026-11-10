module

public import ArtinMatthews.SourceComplexAdelicCharacter
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.VaryingKummerAnalytic
open MeasureTheory NumberField NumberField.InfinitePlace
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]

theorem source_complex_places_nonempty :
    Nonempty {v : InfinitePlace K // IsComplex v} := by
  let v : InfinitePlace K := Classical.arbitrary _
  exact ⟨⟨v, IsTotallyComplex.isComplex v⟩⟩

omit [NumberField K] in
theorem source_complex_real_places_empty : IsEmpty {v : InfinitePlace K // IsReal v} := by
  refine ⟨fun v => ?_⟩
  exact (not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.val)) v.property

omit [NumberField K] in
theorem sourceComplexPlaceAdele_surjective : Function.Surjective (sourceComplexPlaceAdele K) := by
  have := source_complex_real_places_empty K
  intro a
  refine ⟨(InfiniteAdeleRing.ringEquiv_mixedSpace K a).2, ?_⟩
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
  simp only [sourceComplexPlaceAdele, RingEquiv.apply_symm_apply]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

def sourceComplexPlaceAdeleEquiv :
    ({v : InfinitePlace K // IsComplex v} → ℂ) ≃+* InfiniteAdeleRing K where
  toFun := sourceComplexPlaceAdele K
  invFun a := (InfiniteAdeleRing.ringEquiv_mixedSpace K a).2
  left_inv x := by
    change ((InfiniteAdeleRing.ringEquiv_mixedSpace K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x))).2 = x
    rw [RingEquiv.apply_symm_apply]
  right_inv a := by
    obtain ⟨x, rfl⟩ := sourceComplexPlaceAdele_surjective K a
    change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
      (0, ((InfiniteAdeleRing.ringEquiv_mixedSpace K)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x))).2) =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x)
    rw [RingEquiv.apply_symm_apply]
  map_mul' x y := by
    change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x * y) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x) *
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, y)
    rw [← map_mul]
    simp only [Prod.mk_mul_mk, zero_mul]
  map_add' x y := by
    change (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x + y) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, x) +
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (0, y)
    rw [← map_add]
    simp only [Prod.mk_add_mk, zero_add]

/-- The actual mixed-embedding norm is the product of squared complex norms. -/
theorem sourceComplexPlaceAdele_mixed_norm
    (x : {v : InfinitePlace K // IsComplex v} → ℂ) :
    mixedEmbedding.norm (InfiniteAdeleRing.ringEquiv_mixedSpace K (sourceComplexPlaceAdele K x)) =
      sourceComplexProductAbsoluteValue x := by
  let e : InfinitePlace K ≃ {v : InfinitePlace K // IsComplex v} :=
    ⟨fun v => ⟨v, IsTotallyComplex.isComplex v⟩, Subtype.val,
      fun _ => rfl, fun _ => rfl⟩
  rw [mixedEmbedding.norm_apply]
  simp only [sourceComplexPlaceAdele, RingEquiv.apply_symm_apply,
    IsTotallyComplex.mult_eq]
  calc
    _ = ∏ v : InfinitePlace K, ‖x (e v)‖ ^ 2 := by
      apply Finset.prod_congr rfl
      intro v _
      rw [mixedEmbedding.normAtPlace_apply_of_isComplex (IsTotallyComplex.isComplex v)]
      rfl
    _ = _ := e.prod_comp (fun v => ‖x v‖ ^ 2)

theorem sourceNumberFieldComplexFourier_test_zero :
    sourceNumberFieldComplexFourier K sourceComplexProductTest 0 = 0 := by
  have := source_complex_places_nonempty K
  rw [sourceNumberFieldComplexFourier_eq]
  exact sourceComplexProductTest_fourier_zero

end
end ArtinMatthews.VaryingKummerAnalytic
