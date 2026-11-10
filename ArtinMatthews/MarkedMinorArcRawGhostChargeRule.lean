module

public import ArtinMatthews.MarkedMinorArcRawGhostAbsoluteAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The literal indexed ghost rule with its three real charges displayed.
Both the original and swapped actions are exact specializations; the
general charges permit their common factorial-transpose argument. -/
namespace ArtinMatthews
open scoped BigOperators

noncomputable def markedRawGhostChargeCoefficient {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (δ γ s : J → ℝ)
    (m : MarkedRawMemory P B) (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (del : MarkedRawGhostDeletion m) (l : MarkedRawGhostBirthSizes m del) : ℝ :=
  ∏ j,δ j^(del j).card*s j^((markedRawGroupHitIndices m j z hz \ del j).card)*γ j^(l.1 j : ℕ)

/-- Exact original total-truncated choice rule, with only its scalar
charges generalized. Eligibility, targets and measures are unchanged. -/
noncomputable def markedRawGhostMemoryRule {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (f : MarkedRawMemory P B → ℂ) (m : MarkedRawMemory P B) : ℂ := by
  classical
  exact ∑ del : MarkedRawGhostDeletion m,
    if MarkedRawGhostDeletionAllowed m z hz del then
      ∑ l : MarkedRawGhostBirthSizes m del, ∑ births : MarkedRawGhostBirthLabels l,
        ((markedRawGhostChargeCoefficient δ γ s m z hz del l*
          markedRawGhostBirthMass ν l births : ℝ) : ℂ)*
          f (markedRawGhostTargetMemory m z hz del l births)
    else 0

/-- Literal identification with the original full raw-state ghost. -/
theorem markedRawGhostApply_eq_memoryRule {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (t : MarkedRawState P M B Z) :
    markedRawGhostApply ν V qStage ρ hZ f t=
      markedRawGhostMemoryRule ν (fun _ => -(1-qStage)/ρ) (fun j => -(1-qStage)*V j/ρ)
        (fun _ => qStage/ρ^2) t.1.1 (hZ _ t.1.2) (fun m => f (t.1,(t.2.1,m))) t.2.2 := rfl

/-- Literal identification with the actual swapped-charge full rule. -/
theorem markedRawGhostSwappedApply_eq_memoryRule {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ) (t : MarkedRawState P M B Z) :
    markedRawGhostSwappedApply ν V qStage ρ hZ f t=
      markedRawGhostMemoryRule ν (fun j => -(1-qStage)*V j/ρ) (fun _ => -(1-qStage)/ρ)
        (fun _ => qStage/ρ^2) t.1.1 (hZ _ t.1.2) (fun m => f (t.1,(t.2.1,m))) t.2.2 := rfl

end ArtinMatthews
