module

public import ArtinMatthews.MarkedMinorArcRawGhostAbsoluteAction
public import ArtinMatthews.MarkedMinorArcRawGhostEnergyFibers
public import ArtinMatthews.MarkedMinorArcRawGhostMemoryTranspose
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

/-! The proved literal factorial transpose extends to the full physical
state measure by finite Fubini, retaining every active and pending slot. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

/-- Actual original/swapped full-state transpose on the genuine symmetric
pending domain. No adjoint identity or operator bound is a premise. -/
theorem markedRawGhostApply_transpose {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (qStage ρ : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f g : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m))))
    (hg : ∀ z a, MarkedRawMemorySymmetric (fun m => g (z, (a, m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostApply ν V qStage ρ hZ f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s * markedRawGhostSwappedApply ν V qStage ρ hZ g s := by
  classical
  rw [markedRawGhostApply_pairing_fibers, markedRawGhostSwappedApply_pairing_fibers]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact markedRawGhostMemoryRule_transpose ν (fun _ => -(1-qStage)/ρ)
    (fun j => -(1-qStage)*V j/ρ) (fun _ => qStage/ρ^2) z.1 (hZ _ z.2)
    (fun m => f (z, (a, m))) (fun m => g (z, (a, m))) (hf z a) (hg z a)

/-- In the true positive parameter range the literal absolute rules obey
the same exact full-state transpose, by their proved rho-sign identities. -/
theorem markedRawGhostAbsApply_transpose {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (V : J → ℝ) (hV : ∀ j, 0 ≤ V j)
    {qStage ρ : ℝ} (hq₀ : 0 ≤ qStage) (hq₁ : qStage ≤ 1) (hρ : 0 < ρ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f g : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z, (a, m))))
    (hg : ∀ z a, MarkedRawMemorySymmetric (fun m => g (z, (a, m)))) :
    (∑ s, (markedRawStateMass ν s : ℂ) * g s * markedRawGhostAbsApply ν V qStage ρ hZ f s) =
      ∑ s, (markedRawStateMass ν s : ℂ) * f s * markedRawGhostSwappedAbsApply ν V qStage ρ hZ g s := by
  rw [markedRawGhostAbsApply_eq_neg_rho ν hν V hV hq₀ hq₁ hρ,
    markedRawGhostSwappedAbsApply_eq_neg_rho ν hν V hV hq₀ hq₁ hρ]
  exact markedRawGhostApply_transpose ν V qStage (-ρ) hZ f g hf hg

end
end ArtinMatthews
