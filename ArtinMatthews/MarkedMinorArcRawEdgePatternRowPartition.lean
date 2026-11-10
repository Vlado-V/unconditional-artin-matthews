module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternFilteredRows
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

/-! Exact row splitting, before estimates: each choice either promotes
an indexed old prime or has no promoted group. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdgePatternWeightedRow_promotion_split
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A : MarkedRawEdgePatternKernel P pads B Z) (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ s =
      markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀ s +
        markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀ s := by
  unfold markedRawEdgePatternWeightedRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : markedRawEdgeChoicePromoted c = fun _ => false <;>
    simp [markedRawEdgePromotedKernel,markedRawEdgeNoPromotionKernel,markedRawEdgeFlagGate,hp]

theorem markedRawSlotAverageReal_add {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F G : MarkedRawState P M B Z → ℝ) :
    markedRawSlotAverageReal (F+G) = markedRawSlotAverageReal F + markedRawSlotAverageReal G := by
  funext s
  simp only [markedRawSlotAverageReal,Pi.add_apply,Finset.sum_add_distrib,mul_add]

theorem markedRawEdgePatternWeightedRow_average_promotion_split
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A : MarkedRawEdgePatternKernel P pads B Z) (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ A v₀) s =
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀) s +
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀) s := by
  have h : markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ =
      markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀ +
        markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀ := by
    funext u
    exact markedRawEdgePatternWeightedRow_promotion_split ν δ γ hZ A v₀ u
  rw [h,markedRawSlotAverageReal_add]
  rfl

theorem markedRawEdgeStoreOnlyKernel_eq_noPromotion_stored
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeStoreOnlyKernel A = markedRawEdgeNoPromotionKernel (markedRawEdgeStoredKernel A) := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    simp [markedRawEdgeStoreOnlyKernel,markedRawEdgeNoPromotionKernel,
      markedRawEdgeStoredKernel,markedRawEdgeFlagGate,hp,hq]

theorem markedRawEdgeStoreOnlyKernel_reverse
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeStoreOnlyKernel A) =
      markedRawEdgePromotedKernel
        (markedRawEdgeFlagGate (fun _ q => q = fun _ => false) (markedRawEdgePatternReverse A)) := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    simp [markedRawEdgePatternReverse,markedRawEdgeStoreOnlyKernel,
      markedRawEdgePromotedKernel,markedRawEdgeFlagGate,hp,hq]

theorem markedRawEdgeFlagGate_mul
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (J → Bool) → (J → Bool) → Prop) (A K : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeFlagGate F (fun p q s t => A p q s t * K p q s t) =
      (fun p q s t => markedRawEdgeFlagGate F A p q s t * K p q s t) := by
  funext p q s t
  by_cases h : F p q <;> simp [markedRawEdgeFlagGate,h]

end
end ArtinMatthews
