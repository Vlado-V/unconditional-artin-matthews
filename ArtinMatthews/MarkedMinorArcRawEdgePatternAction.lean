module

public import ArtinMatthews.MarkedMinorArcRawEdgeChargedAction
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeFibers
public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeTransport
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

/-! Literal store/promote actions with a joint coefficient depending on
both Boolean flag families.  Source and target cutoffs remain in the
actual choice type; transposition will exchange these two families. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

abbrev MarkedRawEdgePatternKernel {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (pads B : ℕ) (Z : Finset (ℤ × ℤ)) :=
  (J → Bool) → (J → Bool) → MarkedRawState P (pads+1) B Z →
    MarkedRawState P (pads+1) B Z → ℂ

def markedRawEdgeChoicePromoted {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedRawEdgeChoice hZ s) : J → Bool := fun j => (c.promotions j).isSome

def markedRawEdgePatternReverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  fun p q s t => A q p t s

@[simp] theorem markedRawEdgePatternReverse_reverse {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgePatternReverse A) = A := rfl

def markedRawEdgePatternApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (A : MarkedRawEdgePatternKernel P pads B Z)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ c : MarkedRawEdgeChoice hZ s,
    markedRawEdgeChoiceCharge δ γ hZ s c * markedRawEdgeChoiceFreshMass ν hZ s c *
      A (markedRawEdgeChoicePromoted c) c.store s (markedRawEdgeTargetState hZ s c) *
      f (markedRawEdgeTargetState hZ s c)

theorem markedRawEdgePatternApply_const {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (K : MarkedRawState P (pads+1) B Z → MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgePatternApply ν δ γ hZ (fun _ _ => K) f =
      markedRawEdgeChargedApply ν δ γ hZ K f := rfl

theorem markedRawEdge_degree_promoted_flags {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (x : Z) (active : MarkedRawActive P (pads+1))
    (y : Z) (a : MarkedRawEdgeDegreeShape J B)
    (data : MarkedRawEdgeDegreePayload P y.1 (hZ _ y.2) a) :
    markedRawEdgeChoicePromoted (markedRawEdgeDegreeMemoryChoice hZ x active y a data).2 =
      a.1.promoted := by
  funext j
  exact markedRawEdge_degree_promoted hZ x active y a data j

end
end ArtinMatthews
