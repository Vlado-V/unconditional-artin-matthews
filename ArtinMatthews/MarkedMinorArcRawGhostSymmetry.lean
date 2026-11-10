module

public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryTargets
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

/-! The literal signed ghost operator preserves the actual symmetric
pending-memory domain. All old masks, signs, repeated ordered births,
factorial masses and the total cutoff remain in the original operator. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews

theorem markedRawGhostTargetState_symmetric_permute {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) :
    f (markedRawGhostTargetState hZ (z,(a,markedRawMemoryPermute m σ))
      (markedRawGhostDeletionPermute m σ del) (markedRawGhostBirthSizesPermuteEquiv m σ del l) births) =
      f (markedRawGhostTargetState hZ (z,(a,m)) del l births) :=
  markedRawGhostTargetMemory_symmetric_permute (fun m => f (z,(a,m))) (hf z a) m σ
    z.1 (hZ _ z.2) del l births

/-- Exact pending-index permutation invariance of the original signed
ghost row, proved by reindexing its actual masks and birth-size sum. -/
theorem markedRawGhostApply_permute {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) (m : MarkedRawMemory P B)
    (σ : (j : J) → Equiv.Perm (Fin (m.1.1 j : ℕ))) :
    markedRawGhostApply ν V qStage ρ hZ f (z,(a,markedRawMemoryPermute m σ)) =
      markedRawGhostApply ν V qStage ρ hZ f (z,(a,m)) := by
  classical
  unfold markedRawGhostApply
  rw [← Equiv.sum_comp (markedRawGhostDeletionPermuteEquiv m σ)]
  apply Finset.sum_congr rfl
  intro del _
  change (if MarkedRawGhostDeletionAllowed (markedRawMemoryPermute m σ) z.1 (hZ _ z.2)
      (markedRawGhostDeletionPermute m σ del) then _ else 0) =
    (if MarkedRawGhostDeletionAllowed m z.1 (hZ _ z.2) del then _ else 0)
  rw [markedRawGhostDeletionAllowed_permute]
  by_cases hd : MarkedRawGhostDeletionAllowed m z.1 (hZ _ z.2) del
  · rw [ite_eq_left hd, ite_eq_left hd]
    change (∑ l : MarkedRawGhostBirthSizes (markedRawMemoryPermute m σ) (markedRawGhostDeletionPermute m σ del),
      ∑ births : MarkedRawGhostBirthLabels l,
        ((markedRawGhostSignedCoefficient V qStage ρ (markedRawMemoryPermute m σ) z.1 (hZ _ z.2)
          (markedRawGhostDeletionPermute m σ del) l * markedRawGhostBirthMass ν l births : ℝ) : ℂ) *
          f (markedRawGhostTargetState hZ (z,(a,markedRawMemoryPermute m σ))
            (markedRawGhostDeletionPermute m σ del) l births)) = _
    rw [← Equiv.sum_comp (markedRawGhostBirthSizesPermuteEquiv m σ del)]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro births _
    change MarkedRawGhostBirthLabels l at births
    rw [markedRawGhostSignedCoefficient_permute, markedRawGhostBirthMass_permute,
      markedRawGhostTargetState_symmetric_permute hZ f hf]
  · rw [ite_eq_right hd, ite_eq_right hd]

/-- The actual symmetric-pending domain is invariant under the literal
ghost action, without any symmetry assumption on particle values. -/
theorem markedRawGhostApply_symmetric {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ)
    {M B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (f : MarkedRawState P M B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m))))
    (z : Z) (a : MarkedRawActive P M) :
    MarkedRawMemorySymmetric (fun m => markedRawGhostApply ν V qStage ρ hZ f (z,(a,m))) :=
  fun m σ => markedRawGhostApply_permute ν V qStage ρ hZ f hf z a m σ

end ArtinMatthews
