module

public import ArtinMatthews.GiantTwoSidedRawPositionCutoff
public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.GiantTwoSidedPatternDilationBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews
open Filter Finset
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantCandidateSharedProductMax_subpower (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      (giantTwoSidedSharedProductMax P k : ℝ) ≤ x ^ δ := by
  filter_upwards [giantCandidatePatternDilation_subpower k hδ, eventually_gt_atTop (0 : ℝ)]
    with x hD hx
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let C (_ : S) : Finset (Fin k) := ∅
  let aux : GiantTwoSidedPatternAuxiliary P C := fun j i =>
    (Finset.notMem_empty i.val (show i.val ∈ (∅ : Finset (Fin k)) from i.property)).elim
  have haux : giantTwoSidedPatternAuxiliaryProduct aux = 1 := by
    unfold giantTwoSidedPatternAuxiliaryProduct
    apply prod_eq_one
    intro j _
    apply prod_eq_one
    intro i _
    exact (Finset.notMem_empty i.val (show i.val ∈ (∅ : Finset (Fin k)) from i.property)).elim
  have hslot (i : Fin k) : Fin.castAdd 0 i = i := Fin.ext rfl
  have hmark (a : MarkedPhysicalMarking P k) : (markedPhysicalMarkingProduct a : ℝ) ≤ x ^ δ := by
    simpa only [giantTwoSidedPatternDilation, haux, mul_one,
      giantTwoSidedPatternCopiedProduct, C, sdiff_empty, hslot, markedPhysicalMarkingProduct]
      using hD S 0 C a aux
  have hmax : giantTwoSidedSharedProductMax P k ≤ ⌊x ^ δ⌋₊ := by
    unfold giantTwoSidedSharedProductMax
    exact Finset.sup_le fun a _ => Nat.le_floor (hmark a)
  exact (Nat.cast_le.mpr hmax).trans (Nat.floor_le (Real.rpow_nonneg hx.le _))

theorem giantTwoSidedRawPositionBox_union_succ {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (k U : ℕ) :
    giantTwoSidedRawPositionBox P k U ∪ giantTwoSidedRawPositionBox P k (U + 1) =
      Ioc 0 (giantTwoSidedSharedProductMax P k * (U + 1)) := by
  change Ioc 0 (giantTwoSidedSharedProductMax P k * U) ∪
      Ioc 0 (giantTwoSidedSharedProductMax P k * (U + 1)) = _
  apply union_eq_right.mpr
  intro n hn
  obtain ⟨hpos, hcap⟩ := mem_Ioc.mp hn
  exact mem_Ioc.mpr ⟨hpos, hcap.trans (Nat.mul_le_mul_left _ (Nat.le_succ U))⟩

theorem giantCandidateRawPositionBox_cap_eventually (k : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᶠ x : ℝ in atTop, ∀ S : Finset (GiantCandidateGroupIndex x),
      let P (i : S) := giantCandidateGroup x i.val
      let U := ⌊T * x⌋₊
      let N := giantTwoSidedSharedProductMax P k * (U + 1)
      (N : ℝ) ≤ x ^ 2 ∧
        giantTwoSidedRawPositionBox P k U ∪ giantTwoSidedRawPositionBox P k (U + 1) ⊆
          Ioc 0 ⌊x ^ 2⌋₊ := by
  filter_upwards [giantCandidateSharedProductMax_subpower k (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop (1 : ℝ), Real.tendsto_sqrt_atTop.eventually_ge_atTop (T + 1)]
    with x hD hx hsqrt
  intro S
  let P (i : S) := giantCandidateGroup x i.val
  let U := ⌊T * x⌋₊
  let N := giantTwoSidedSharedProductMax P k * (U + 1)
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hD' : (giantTwoSidedSharedProductMax P k : ℝ) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact hD S
  have hU : ((U + 1 : ℕ) : ℝ) ≤ (T + 1) * x := by
    have hfloor : (U : ℝ) ≤ T * x := Nat.floor_le (mul_nonneg hT.le hx0)
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    exact add_le_add hfloor hx
  have hcap : (N : ℝ) ≤ x ^ 2 := by
    calc
      (N : ℝ) = (giantTwoSidedSharedProductMax P k : ℝ) * ((U + 1 : ℕ) : ℝ) :=
        Nat.cast_mul _ _
      _ ≤ Real.sqrt x * ((T + 1) * x) :=
        mul_le_mul hD' hU (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt x * (Real.sqrt x * x) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt hx0) (Real.sqrt_nonneg _)
      _ = x ^ 2 := by rw [← mul_assoc, ← sq, Real.sq_sqrt hx0, sq]
  refine ⟨hcap, ?_⟩
  rw [giantTwoSidedRawPositionBox_union_succ]
  intro n hn
  obtain ⟨hpos, hnN⟩ := mem_Ioc.mp hn
  exact mem_Ioc.mpr ⟨hpos, hnN.trans (Nat.le_floor hcap)⟩

end
end ArtinMatthews
