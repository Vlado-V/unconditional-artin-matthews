module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternSymmetrized
public import ArtinMatthews.MarkedMinorArcRawEdgeSectors
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
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact additive partitions of the literal flag action.  Dirty means
the complement of the all-fresh, no-store sector. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeFlagGate {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (J → Bool) → (J → Bool) → Prop) (A : MarkedRawEdgePatternKernel P pads B Z) :
    MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => if F p q then A p q s t else 0

def markedRawEdgePromotedKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  markedRawEdgeFlagGate (fun p _ => p ≠ fun _ => false) A

def markedRawEdgeStoredKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  markedRawEdgeFlagGate (fun _ q => q ≠ fun _ => false) A

def markedRawEdgeStoreOnlyKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  markedRawEdgeFlagGate (fun p q => p = (fun _ => false) ∧ q ≠ fun _ => false) A

def markedRawEdgeDirtyKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  markedRawEdgeFlagGate (fun p q => markedRawEdgeClassify p q ≠ .clean) A

theorem markedRawEdgeFlagGate_source_symmetric
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (J → Bool) → (J → Bool) → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hA : ∀ p q z a t, MarkedRawMemorySymmetric (fun m => A p q (z,(a,m)) t))
    (p q : J → Bool) (z : Z) (a : MarkedRawActive P (pads+1)) (t : MarkedRawState P (pads+1) B Z) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeFlagGate F A p q (z,(a,m)) t) := by
  intro m σ
  unfold markedRawEdgeFlagGate
  split_ifs
  · exact hA p q z a t m σ
  · rfl

theorem markedRawEdgeFlagGate_target_symmetric
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (J → Bool) → (J → Bool) → Prop) (A : MarkedRawEdgePatternKernel P pads B Z)
    (hA : ∀ p q s z a, MarkedRawMemorySymmetric (fun m => A p q s (z,(a,m))))
    (p q : J → Bool) (s : MarkedRawState P (pads+1) B Z) (z : Z) (a : MarkedRawActive P (pads+1)) :
    MarkedRawMemorySymmetric (fun m => markedRawEdgeFlagGate F A p q s (z,(a,m))) := by
  intro m σ
  unfold markedRawEdgeFlagGate
  split_ifs
  · exact hA p q s z a m σ
  · rfl

theorem markedRawEdgePromotedKernel_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgePromotedKernel A) =
      markedRawEdgeStoredKernel (markedRawEdgePatternReverse A) := rfl

theorem markedRawEdgeStoreOnlyKernel_eq_sector {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeStoreOnlyKernel A = markedRawEdgeSectorKernel .storeOnly A := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    by_cases ho : MarkedRawEdgeFlagsOverlap p q <;>
    simp [markedRawEdgeStoreOnlyKernel, markedRawEdgeFlagGate,
      markedRawEdgeSectorKernel, markedRawEdgeClassify, hp, hq, ho]

theorem markedRawEdgeDirtyKernel_eq_promoted_add_storeOnly {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeDirtyKernel A = markedRawEdgePromotedKernel A + markedRawEdgeStoreOnlyKernel A := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    by_cases ho : MarkedRawEdgeFlagsOverlap p q <;>
    simp [markedRawEdgeDirtyKernel, markedRawEdgePromotedKernel,
      markedRawEdgeStoreOnlyKernel, markedRawEdgeFlagGate, markedRawEdgeClassify, hp, hq, ho]

theorem markedRawEdgeDirtyKernel_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeDirtyKernel A) =
      markedRawEdgeDirtyKernel (markedRawEdgePatternReverse A) := by
  funext p q s t
  have hc : markedRawEdgeClassify q p = .clean ↔ markedRawEdgeClassify p q = .clean := by
    simp only [markedRawEdgeClassify_clean_iff, and_comm]
  simp only [markedRawEdgePatternReverse,markedRawEdgeDirtyKernel,markedRawEdgeFlagGate,ne_eq,hc]
  by_cases h : markedRawEdgeClassify p q = .clean <;> simp [h]

theorem markedRawEdgePatternKernel_eq_clean_add_dirty {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    A = markedRawEdgeSectorKernel .clean A + markedRawEdgeDirtyKernel A := by
  funext p q s t
  by_cases hc : markedRawEdgeClassify p q = .clean <;>
    simp [markedRawEdgeSectorKernel,markedRawEdgeDirtyKernel,markedRawEdgeFlagGate,hc]

theorem markedRawEdgeDirtyKernel_eq_four_sectors {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeDirtyKernel A =
      markedRawEdgeSectorKernel .storeOnly A + markedRawEdgeSectorKernel .promoteOnly A +
        markedRawEdgeSectorKernel .disjoint A + markedRawEdgeSectorKernel .overlap A := by
  funext p q s t
  cases hc : markedRawEdgeClassify p q <;>
    simp [markedRawEdgeDirtyKernel,markedRawEdgeFlagGate,markedRawEdgeSectorKernel,hc]

theorem markedRawEdgePatternApply_add {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (A₁ A₂ : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternApply ν δ γ hZ (A₁+A₂) f =
      markedRawEdgePatternApply ν δ γ hZ A₁ f + markedRawEdgePatternApply ν δ γ hZ A₂ f := by
  funext s
  simp only [markedRawEdgePatternApply,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem markedRawSlotAverage_add {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (f g : MarkedRawState P M B Z → ℂ) :
    markedRawSlotAverage (f+g) = markedRawSlotAverage f + markedRawSlotAverage g := by
  funext s
  simp only [markedRawSlotAverage,Pi.add_apply,Finset.sum_add_distrib,mul_add]

theorem markedRawEdgePatternSymmetrized_add {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (A₁ A₂ : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternSymmetrized ν δ γ hZ (A₁+A₂) f =
      markedRawEdgePatternSymmetrized ν δ γ hZ A₁ f +
        markedRawEdgePatternSymmetrized ν δ γ hZ A₂ f := by
  unfold markedRawEdgePatternSymmetrized
  rw [markedRawEdgePatternApply_add,markedRawSlotAverage_add]

theorem markedRawEdgeDirtySymmetrized_eq_promoted_add_storeOnly
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternSymmetrized ν δ γ hZ (markedRawEdgeDirtyKernel A) f =
      markedRawEdgePatternSymmetrized ν δ γ hZ (markedRawEdgePromotedKernel A) f +
        markedRawEdgePatternSymmetrized ν δ γ hZ (markedRawEdgeStoreOnlyKernel A) f := by
  rw [markedRawEdgeDirtyKernel_eq_promoted_add_storeOnly,markedRawEdgePatternSymmetrized_add]

end
end ArtinMatthews
