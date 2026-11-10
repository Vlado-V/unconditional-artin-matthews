module

public import ArtinMatthews.MarkedMinorArcRawGhostChargeRule
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

/-! Exact finite disintegration of the full raw-state pairing into fixed
position and active-slot fibers with the genuine factorial memory measure. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

/-- Position has counting measure; active-slot mass factors out of each
literal memory fiber, without a state-count factor. -/
theorem markedRawStateMass_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) * f (z, (a, m)) := by
  classical
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  simp only [markedRawStateMass, Complex.ofReal_mul]
  ring

/-- Full-state original ghost pairing is exactly its actual memory rule on
fixed position/active fibers. -/
theorem markedRawGhostApply_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostApply ν V qStage ρ hZ f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) *
          markedRawGhostMemoryRule ν (fun _ => -(1-qStage)/ρ) (fun j => -(1-qStage)*V j/ρ)
            (fun _ => qStage/ρ^2) z.1 (hZ _ z.2) (fun m => f (z, (a, m))) m :=
  markedRawStateMass_pairing_fibers ν (markedRawGhostApply ν V qStage ρ hZ f) g

/-- The swapped-charge action has the same exact physical fiber measure. -/
theorem markedRawGhostSwappedApply_pairing_fibers {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f g : MarkedRawState P M B Z → ℂ) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostSwappedApply ν V qStage ρ hZ f s) =
      ∑ z : Z, ∑ a : MarkedRawActive P M, (markedRawActiveMass ν a : ℂ) *
        ∑ m : MarkedRawMemory P B, (markedRawMemoryMass ν m : ℂ) * g (z, (a, m)) *
          markedRawGhostMemoryRule ν (fun j => -(1-qStage)*V j/ρ) (fun _ => -(1-qStage)/ρ)
            (fun _ => qStage/ρ^2) z.1 (hZ _ z.2) (fun m => f (z, (a, m))) m :=
  markedRawStateMass_pairing_fibers ν (markedRawGhostSwappedApply ν V qStage ρ hZ f) g

end
end ArtinMatthews
