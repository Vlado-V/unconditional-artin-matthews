module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarResidual
public import ArtinMatthews.MarkedMemoryHistoryAnchorGates
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

/-! The literal ordered edge residual already carries the copied-line
anchor gate. Nonzero residuals force actual anchor admissibility even
when a separate ghost scalar vanishes. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)

theorem markedMemoryEdgeAnchorGate_of_residual_ne_zero
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (edge : MarkedMemoryEdgeChoice hZ s)
    (hr : markedMemoryEdgeResidual hZ ψ η d₀ Y Q χ s edge≠0) :
    MarkedMemoryEdgeAnchorGate hZ s edge := by
  have hc : markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q 1 χ (markedRawSlotEquiv edge.1 s) edge.2.1≠0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hr).1).2
  exact markedMemoryRawEdgeAnchorGate_of_coefficient_ne_zero hZ ψ η d₀ Y Q 1 χ _ _ hc

theorem markedMemoryHistoryAnchorAdmissible_of_edgeResidual_ne_zero
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (n k : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s)
    (hr : markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n k H≠0) :
    MarkedMemoryHistoryAnchorAdmissible hZ H := by
  induction n generalizing k s with
  | zero => trivial
  | succ n ih =>
    have hp := mul_ne_zero_iff.mp hr
    exact ⟨markedMemoryEdgeAnchorGate_of_residual_ne_zero hZ ψ η d₀ Y Q (χ k) _ _ hp.1,
      ih (k+1) H.2.2 hp.2⟩

theorem markedMemoryHistoryEdgeResidual_zero_of_not_anchor
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (n k : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (H : MarkedMemoryChronologicalHistory hZ n s)
    (ha : ¬MarkedMemoryHistoryAnchorAdmissible hZ H) :
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n k H=0 := by
  by_contra hr
  exact ha (markedMemoryHistoryAnchorAdmissible_of_edgeResidual_ne_zero hZ ψ η d₀ Y Q χ n k H hr)

end
end ArtinMatthews
