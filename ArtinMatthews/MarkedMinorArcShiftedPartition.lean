module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import ArtinMatthews.MarkedMinorArcCompression
public import ArtinMatthews.MarkedMinorArcRectangular
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite coordinate energy for a partition translated injectively
in an arbitrary key type. Only the finite image of the keys is summed. -/
namespace ArtinMatthews

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Literal rectangular block from one row class to its translated column class. -/
def markedMinorShiftedClassBlock {X κ : Type*} (A : Matrix X X ℂ)
    (key : X → κ) (e : κ → κ) (k : κ) :
    Matrix {i : X // key i=k} {j : X // key j=e k} ℂ := A.submatrix Subtype.val Subtype.val

theorem markedMinorShiftedClassBlock_mulVec {X κ : Type*} [Fintype X] [DecidableEq κ]
    (A : Matrix X X ℂ) (key : X → κ) (e : κ → κ)
    (hsupport : ∀ i j, key j ≠ e (key i) → A i j=0)
    (f : X → ℂ) (k : κ) (i : {i : X // key i=k}) :
    (A *ᵥ f) i.1 = (markedMinorShiftedClassBlock A key e k *ᵥ fun j => f j.1) i := by
  classical
  unfold Matrix.mulVec dotProduct
  rw [markedMinorSum_injective (Subtype.val : {j : X // key j=e k} → X) Subtype.val_injective _ ?_]
  · rfl
  · intro j hj
    have hn : key j ≠ e k := fun h => hj ⟨⟨j,h⟩,rfl⟩
    change A i.1 j*f j=0
    exact mul_eq_zero_of_left (hsupport i.1 j (by simpa only [i.2] using hn)) (f j)

theorem markedMinorKeyFiber_sum {X κ : Type*} [Fintype X] [DecidableEq κ]
    (key : X → κ) (k : κ) (f : X → ℝ) :
    (∑ i : {i : X // key i=k}, f i.1) = ∑ i ∈ Finset.univ.filter (fun i => key i=k), f i := by
  classical
  exact (Finset.sum_subtype _ (by simp) f).symm

theorem markedMinorKey_partition_sum {X κ : Type*} [Fintype X] [DecidableEq κ]
    (key : X → κ) (f : X → ℝ) :
    (∑ k ∈ Finset.univ.image key, ∑ i : {i : X // key i=k}, f i.1) = ∑ i, f i := by
  classical
  simp_rw [markedMinorKeyFiber_sum]
  exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) f

theorem markedMinorShiftedKey_partition_le {X κ : Type*} [Fintype X] [DecidableEq κ]
    (key : X → κ) (e : κ → κ) (he : Function.Injective e)
    (f : X → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ k ∈ Finset.univ.image key, ∑ j : {j : X // key j=e k}, f j.1) ≤ ∑ j, f j := by
  classical
  simp_rw [markedMinorKeyFiber_sum]
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  let S := (Finset.univ.image key).filter (fun k => key j=e k)
  have hc : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro k hk l hl
    exact he ((Finset.mem_filter.mp hk).2.symm.trans (Finset.mem_filter.mp hl).2)
  calc
    _ = ∑ _k ∈ S, f j := by simp only [S,Finset.sum_filter]
    _ = (S.card:ℝ)*f j := by simp
    _ ≤ 1*f j := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (hf j)
    _ = _ := one_mul _

/-- Injective translation of the column classes preserves the uniform
rectangular block bound, even when the class-key type is infinite. -/
theorem markedMinorShiftedPartition_norm_le {X κ : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq κ]
    (A : Matrix X X ℂ) (key : X → κ) (e : κ → κ) (he : Function.Injective e)
    (hsupport : ∀ i j, key j ≠ e (key i) → A i j=0)
    {C : ℝ} (hC : 0 ≤ C)
    (hblocks : ∀ k, ‖markedMinorShiftedClassBlock A key e k‖ ≤ C) : ‖A‖ ≤ C := by
  classical
  apply markedMinorRectangular_norm_le_of_energy _ hC
  intro f
  calc
    _ = ∑ k ∈ Finset.univ.image key, ∑ i : {i : X // key i=k}, ‖(A *ᵥ f) i.1‖^2 :=
      (markedMinorKey_partition_sum key (fun i => ‖(A *ᵥ f) i‖^2)).symm
    _ ≤ ∑ k ∈ Finset.univ.image key, C^2*∑ j : {j : X // key j=e k}, ‖f j.1‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      simp only [markedMinorShiftedClassBlock_mulVec A key e hsupport f]
      exact markedMinorRectangular_energy_le_of_norm (markedMinorShiftedClassBlock A key e k)
        hC (hblocks k) (fun j => f j.1)
    _ = C^2*∑ k ∈ Finset.univ.image key, ∑ j : {j : X // key j=e k}, ‖f j.1‖^2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (markedMinorShiftedKey_partition_le key e he (fun j => ‖f j‖^2) (fun _ => sq_nonneg _)) (sq_nonneg C)

theorem markedMinorShiftedPartition_norm_le_of_nonempty_blocks {X κ : Type*}
    [Fintype X] [DecidableEq X] [DecidableEq κ]
    (A : Matrix X X ℂ) (key : X → κ) (e : κ → κ) (he : Function.Injective e)
    (hsupport : ∀ i j, key j ≠ e (key i) → A i j=0)
    {C : ℝ} (hC : 0 ≤ C)
    (hblocks : ∀ k, Nonempty {i : X // key i=k} →
      ‖markedMinorShiftedClassBlock A key e k‖ ≤ C) : ‖A‖ ≤ C := by
  classical
  apply markedMinorShiftedPartition_norm_le A key e he hsupport hC
  intro k
  by_cases hk : Nonempty {i : X // key i=k}
  · exact hblocks k hk
  · let : IsEmpty {i : X // key i=k} := ⟨fun i => hk ⟨i⟩⟩
    have hz : markedMinorShiftedClassBlock A key e k=0 := by
      ext i j
      exact isEmptyElim i
    rw [hz,norm_zero]
    exact hC

end ArtinMatthews
