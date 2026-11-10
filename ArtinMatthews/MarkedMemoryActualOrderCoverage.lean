module

public import ArtinMatthews.MarkedMemoryActualHistoryReconstruction
public import ArtinMatthews.MarkedMemoryIndependentOrderMultiplicity
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

/-! The original history lies in the reconstructed slot-order family of
its extracted independent tableau. This family has its proved exact
factorial cardinality and retains every coefficient and observable. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)
  (ha : MarkedMemoryHistoryAnchorAdmissible hZ history)

def markedMemoryActualOrderHistory (ordering : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryChronologicalHistory hZ n s :=
  markedMemoryHistoryTransport hZ (markedMemoryActualTableau_initial hZ history ha)
    (markedMemoryIndependentHistory hZ (markedMemoryActualTableau hZ history ha) ordering)

omit [DecidableEq J] in
theorem markedMemoryHistoryTransport_injective {s t : MarkedRawState P (pads+1) B Z} (h : s = t) :
    Function.Injective (markedMemoryHistoryTransport hZ (n := n) h) := by
  cases h
  exact Function.injective_id

theorem markedMemoryActualOrderHistory_injective :
    Function.Injective (markedMemoryActualOrderHistory hZ history ha) := by
  intro a b hab
  apply markedMemoryIndependentHistory_order_injective hZ (markedMemoryActualTableau hZ history ha)
  exact markedMemoryHistoryTransport_injective hZ (markedMemoryActualTableau_initial hZ history ha) hab

def markedMemoryActualOrderHistoryEquiv :
    (Fin n → J → Equiv.Perm (Fin pads)) ≃ Set.range (markedMemoryActualOrderHistory hZ history ha) :=
  Equiv.ofInjective (markedMemoryActualOrderHistory hZ history ha) (markedMemoryActualOrderHistory_injective hZ history ha)

instance markedMemoryActualOrderHistory_fintype : Fintype (Set.range (markedMemoryActualOrderHistory hZ history ha)) :=
  Fintype.ofEquiv _ (markedMemoryActualOrderHistoryEquiv hZ history ha)

theorem markedMemoryActualOrderHistory_covers : history ∈ Set.range (markedMemoryActualOrderHistory hZ history ha) :=
  markedMemoryActualHistory_covered hZ history ha

theorem markedMemoryActualOrderHistory_card :
    Nat.card (Set.range (markedMemoryActualOrderHistory hZ history ha)) =
      (pads.factorial ^ Fintype.card J) ^ n := by
  rw [← Nat.card_congr (markedMemoryActualOrderHistoryEquiv hZ history ha),Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun,Fintype.card_perm,Fintype.card_fin]

theorem markedMemoryActualOrderHistory_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryChronologicalHistory hZ n s → R) :
    (∑ ordering : Fin n → J → Equiv.Perm (Fin pads), F (markedMemoryActualOrderHistory hZ history ha ordering)) =
      ∑ h : Set.range (markedMemoryActualOrderHistory hZ history ha), F h.1 :=
  Equiv.sum_comp (markedMemoryActualOrderHistoryEquiv hZ history ha) (fun h => F h.1)


/-- The literal signed chronological weight, with all its factorial and
slot normalizations, reindexes with an arbitrary ordered target test. -/
theorem markedMemoryActualOrderHistory_weighted_sum
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (F : MarkedRawState P (pads+1) B Z → ℂ) :
    (∑ ordering : Fin n → J → Equiv.Perm (Fin pads),
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j
        (markedMemoryActualOrderHistory hZ history ha ordering) *
      F (markedMemoryChronologicalTarget hZ (markedMemoryActualOrderHistory hZ history ha ordering))) =
    ∑ h : Set.range (markedMemoryActualOrderHistory hZ history ha),
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h.1 *
        F (markedMemoryChronologicalTarget hZ h.1) :=
  markedMemoryActualOrderHistory_sum hZ history ha
    (fun h => markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h *
      F (markedMemoryChronologicalTarget hZ h))

end
end ArtinMatthews
