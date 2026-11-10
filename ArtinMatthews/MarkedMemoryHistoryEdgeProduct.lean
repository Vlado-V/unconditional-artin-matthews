module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarResidual
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
public import Mathlib.RingTheory.WittVector.IsPoly
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal edge-coefficient product before either copied-slot
normalization. Both original inverse slot cardinalities are extracted
at every actual edge, with all tests and actual local choices unchanged. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

def markedMemoryHistoryRawEdgeProduct :
    (n offset : ℕ) → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 1
  | n+1,offset,s,H =>
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 (χ offset)
        (markedRawSlotEquiv H.2.1.1 (markedMemoryGhostChoiceTarget hZ s H.1)) H.2.1.2.1 *
      markedMemoryHistoryRawEdgeProduct n (offset+1) H.2.2

theorem markedMemoryHistoryEdgeResidualProduct_raw
    (n offset : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset H =
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n) *
        markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n offset H := by
  induction n generalizing s offset with
  | zero => simp only [Nat.mul_zero,pow_zero,one_mul]; rfl
  | succ n ih =>
    change markedMemoryEdgeResidual hZ ψ η d₀ Y Q (χ offset)
      (markedMemoryGhostChoiceTarget hZ s H.1) H.2.1 *
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n (offset+1) H.2.2 = _
    rw [ih,show 2*(n+1)=2+2*n by omega,pow_add,pow_two]
    simp only [markedMemoryEdgeResidual]
    conv_rhs => rw [markedMemoryHistoryRawEdgeProduct]
    ring

end
end ArtinMatthews
