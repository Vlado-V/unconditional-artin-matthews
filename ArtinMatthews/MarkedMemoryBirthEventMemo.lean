module

public import ArtinMatthews.MarkedMemoryBirthEventPositive
public import ArtinMatthews.MarkedMemoryHistoryPivotCompatible
public import ArtinMatthews.MarkedMemoryMemoGates
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

/-! The original permutation-event boundary is dominated by the
positive conditional word. Actual chronological memo theorems discharge
every gate and compatibility premise in the finite comparison. -/

noncomputable section
namespace ArtinMatthews

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_le_positive_actual
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z) :
    ‖markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀‖ ≤
      markedMemoryPositivePivotBoundary ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ := by
  apply markedMemoryBirthEventBoundary_le_positive ν hν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀
  · intro s h he
    exact markedMemoryHistory_initial_stageGate hZ h σ he
  · intro s h he
    rw [markedMemoryHistory_initialPivotValues hZ h]
    exact markedMemoryHistory_pivotCompatible hZ h σ he

end ArtinMatthews
