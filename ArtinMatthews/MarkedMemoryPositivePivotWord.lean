module

public import ArtinMatthews.MarkedMemoryPositivePivotOperators
public import ArtinMatthews.MarkedMinorArcRawEdgeGeometricAdjoint
public import ArtinMatthews.MarkedWeightedConditionalKernel
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

/-! The genuine positive alternating word on state and chronological
prime memo. Outside-horizon branches are zero and are never visited by
the full N-edge word started at zero. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedMemoryPositiveGhostPivotAt
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage : ℕ → ℝ) (ρ : ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (j : ℕ)
    (f : (MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) →
      MarkedRawState P (pads+1) B Z → ℝ)
    (old : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  if hj : j<N+1 then markedMemoryPositiveGhostPivot ν V (qStage j) ρ hZ σ ⟨j,hj⟩ f old s else 0

def markedMemoryPositiveEdgePivotAt
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (j : ℕ)
    (f : (MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) →
      MarkedRawState P (pads+1) B Z → ℝ)
    (old : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes)
    (s : MarkedRawState P (pads+1) B Z) : ℝ :=
  if hj : j<N then
    if orientation j then markedMemoryPositiveEdgePivot ν V hZ (markedRawEdgeAdjointCutoff ψ)
      (fun u => star (η u)) d₀ Y Q ρ (fun s => star (χ j s)) σ ⟨j,hj⟩ f old s
    else markedMemoryPositiveEdgePivot ν V hZ ψ η d₀ Y Q ρ (χ j) σ ⟨j,hj⟩ f old s
  else 0

def markedMemoryPositivePivotWord
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) :=
  markedConditionalWord (markedMemoryPositiveGhostPivotAt ν V qStage ρ hZ σ)
    (markedMemoryPositiveEdgePivotAt ν V hZ ψ η d₀ Y Q ρ orientation χ σ)

end ArtinMatthews
