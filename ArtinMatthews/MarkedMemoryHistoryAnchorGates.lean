module

public import ArtinMatthews.MarkedMemoryHistoryEdgeSlotAnchors
public import ArtinMatthews.MarkedMemoryHistoryChronological
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The anchor gate is not an assumed coherence condition: it is extracted
from the literal determinant-divisibility branch of each nonzero raw edge
coefficient and hence from every nonzero chronological history weight. -/
namespace ArtinMatthews
noncomputable section

 theorem markedRawEdgeChoiceCoefficient_eq_zero_of_not_anchorGate
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hg : ¬MarkedMemoryRawEdgeAnchorGate hZ s choice) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice = 0 := by
  change ¬(markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1 : ℤ) ∣
    markedMinorIntegerDet s.1.1 choice.target.1 at hg
  simp [markedRawEdgeChoiceCoefficient, markedRawEdgeTargetState, hg]

 theorem markedMemoryRawEdgeAnchorGate_of_coefficient_ne_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedRawEdgeChoice hZ s)
    (hc : markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s choice ≠ 0) :
    MarkedMemoryRawEdgeAnchorGate hZ s choice := by
  by_contra hg
  exact hc (markedRawEdgeChoiceCoefficient_eq_zero_of_not_anchorGate hZ ψ η d₀ Y Q ρ χ s choice hg)

 theorem markedMemoryEdgeAnchorGate_of_weight_ne_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedMemoryEdgeChoice hZ s)
    (hw : markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s choice ≠ 0) :
    MarkedMemoryEdgeAnchorGate hZ s choice := by
  apply markedMemoryRawEdgeAnchorGate_of_coefficient_ne_zero hZ ψ η d₀ Y Q ρ χ
    (markedRawSlotEquiv choice.1 s) choice.2.1
  intro hc
  apply hw
  simp only [markedMemoryEdgeChoiceWeight, hc, mul_zero, zero_mul]

 def MarkedMemoryHistoryAnchorAdmissible {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → Prop
  | 0, _, _ => True
  | _+1, s, history =>
      MarkedMemoryEdgeAnchorGate hZ (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 ∧
        MarkedMemoryHistoryAnchorAdmissible hZ history.2.2

 theorem markedMemoryHistoryAnchorAdmissible_of_weight_ne_zero
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hw : markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history ≠ 0) :
    MarkedMemoryHistoryAnchorAdmissible hZ history := by
  induction n generalizing j s with
  | zero => trivial
  | succ n ih =>
    have hp := mul_ne_zero_iff.mp hw
    have he := (mul_ne_zero_iff.mp hp.1).2
    exact ⟨markedMemoryEdgeAnchorGate_of_weight_ne_zero ν V hZ ψ η d₀ Y Q ρ (χ j)
      (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1 he,
      ih (j+1) history.2.2 hp.2⟩

end
end ArtinMatthews
