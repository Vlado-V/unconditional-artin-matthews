module

public import ArtinMatthews.MarkedMemoryHistoryEdgeProduct
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
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

/-! The exact raw edge product is the finite product over the literal
chronological edge accessors. This exposes every copied-slot decoration
without replacing any local coefficient or test. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

def markedMemoryRawEdgeValue (χ : MarkedRawState P (pads+1) B Z → ℂ)
    {s : MarkedRawState P (pads+1) B Z} (edge : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ (markedRawSlotEquiv edge.1 s) edge.2.1

theorem markedMemoryRawEdgeValue_heq (χ : MarkedRawState P (pads+1) B Z → ℂ)
    {s t : MarkedRawState P (pads+1) B Z} (hs : s=t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t) (hab : HEq a b) :
    markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ a = markedMemoryRawEdgeValue hZ ψ η d₀ Y Q χ b := by
  cases hs
  have he : a=b := eq_of_heq hab
  cases he
  rfl

theorem markedMemoryHistoryRawEdgeProduct_vertices
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (n offset : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n offset H =
      ∏ v : Fin n,markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ (offset+v.val))
        (markedMemoryHistoryVertexEdge hZ H v) := by
  induction n generalizing s offset with
  | zero => simp [markedMemoryHistoryRawEdgeProduct]
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    change markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ offset) H.2.1 *
      markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n (offset+1) H.2.2 =
      markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ offset) H.2.1 *
        ∏ v : Fin n,markedMemoryRawEdgeValue hZ ψ η d₀ Y Q (χ (offset+(v.val+1)))
          (markedMemoryHistoryVertexEdge hZ H.2.2 v)
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    rw [show (offset+1)+v.val=offset+(v.val+1) by omega]

end
end ArtinMatthews
