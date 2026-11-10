module

public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarResidual
public import ArtinMatthews.MarkedMemoryTransitionAssembly
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

/-! Source-state transport leaves the literal chronological weight
and its ordered residual unchanged. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
  {s t : MarkedRawState P (pads+1) B Z} (hs : s=t) (H : MarkedMemoryChronologicalHistory hZ n s)

theorem markedMemoryChronologicalWeight_transport [DecidableEq J]
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset (markedMemoryHistoryTransport hZ hs H)=
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n offset H := by
  cases hs
  rfl

theorem markedMemoryHistoryEdgeResidual_transport [DecidableEq J]
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset (markedMemoryHistoryTransport hZ hs H)=
      markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n offset H := by
  cases hs
  rfl

end
end ArtinMatthews
