module

public import ArtinMatthews.MarkedMemoryInitialPivotMass
public import ArtinMatthews.MarkedMemoryBirthAtom
public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedRawBoundaryWeightedSource
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original empty-memory source boundary with its initial pivot
constraints. Every ordered active atom and its exact Schur factor are
accounted for before the conditional history is iterated. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryInitialPivot_source_bound
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p)
    {Δ D : ℝ} (hΔ : 0 ≤ Δ) (hD : 1 ≤ D)
    (hatom : ∀ j p,ν j p ≤ Δ) (hmass : ∀ j,(∑ p : P j,ν j p) ≤ D)
    {M B N : ℕ} {Z : Finset (ℤ × ℤ)} (z₀ : Z) (v₀ : ℝ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes) :
    (∑ s : MarkedRawState P M B Z,
      markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*markedRawMemorySchurWeight v₀ s.2.2*
        (if markedMemoryInitialPivotGate σ old s.2.1 then 1 else 0)) ≤
      Δ^(markedMemoryStageNonpivots σ 0).card*D^(Fintype.card J*M) := by
  erw [markedRawBoundary_weighted_source_sum ν z₀ v₀
    (fun a => if markedMemoryInitialPivotGate σ old a then (1:ℝ) else 0)]
  have heq : (∑ a : MarkedRawActive P M,
      markedRawActiveMass ν a*(if markedMemoryInitialPivotGate σ old a then 1 else 0))=
      ∑ a : MarkedRawActive P M,
        if markedMemoryInitialPivotGate σ old a then markedRawActiveMass ν a else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp only [mul_one,mul_zero]
  rw [heq]
  exact markedMemoryInitialPivot_mass_le ν hν hΔ hD hatom hmass σ old

theorem markedMemoryInitialPivot_actual_source_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop, ∀ q : ℝ, 0 ≤ q → q ≤ 1 →
      ∀ (M B N : ℕ) (Z : Finset (ℤ × ℤ)) (z₀ : Z) (v₀ : ℝ)
        (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
        (old : MarkedMemoryPotentialAddress J M B N → Option Nat.Primes),
      (∑ s : MarkedRawState (markedRawActualPrimeBand e x) M B Z,
        markedRawStateMass (markedRawActualPrimeAtom e q x) s*‖markedRawBoundary z₀ s‖*
          markedRawMemorySchurWeight v₀ s.2.2*
          (if markedMemoryInitialPivotGate σ old s.2.1 then 1 else 0)) ≤
        (markedMemoryBirthAtomEnvelope x)^(markedMemoryStageNonpivots σ 0).card*
          (2:ℝ)^(Fintype.card J*M) := by
  filter_upwards [markedMemoryBirthAtom_actual_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hatom hmass
  intro q hq₀ hq₁ M B N Z z₀ v₀ σ old
  exact markedMemoryInitialPivot_source_bound (markedRawActualPrimeAtom e q x)
    (fun j p => (hatom q hq₀ hq₁ j p).1) (markedMemoryBirthAtomEnvelope_pos x).le
    (by norm_num : (1:ℝ) ≤ 2) (fun j p => (hatom q hq₀ hq₁ j p).2)
    (hmass q hq₀ hq₁) z₀ v₀ σ old

end ArtinMatthews
