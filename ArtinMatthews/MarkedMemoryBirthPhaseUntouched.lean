module

public import ArtinMatthews.MarkedMemoryBirthPhaseOperators
public import ArtinMatthews.MarkedMinorArcRawEdgeModifierSymmetrized
public import ArtinMatthews.MarkedMinorArcRawEdgeActualPartition
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! An operation outside the moved-address image is exactly the original
operation, with its physical cutoffs and charges unchanged. In particular
the signed good-edge estimate remains available on every untouched edge. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedMemoryGhostBirthPhaseApply_untouched
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ) {M B n : ℕ}
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (ht : some (2*t.1) ∉ σ.support.image markedMemoryPotentialOperation)
    (f : MarkedRawState P M B Z → ℂ) :
    markedRawGhostBirthModifiedApply ν V qStage ρ hZ (markedMemoryGhostBirthPhase σ θ t) f =
      markedRawGhostApply ν V qStage ρ hZ f := by
  funext s
  unfold markedRawGhostBirthModifiedApply markedRawGhostModifiedApply
  simp_rw [markedMemoryGhostBirthPhase_eq_one σ θ t ht,one_mul]
  exact markedMemoryGhostChoice_sum ν V qStage ρ hZ f s

theorem markedMemoryEdgeBirthPhaseApply_untouched
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B n : ℕ}
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) (t : Fin n)
    (ht : some (2*t.1+1) ∉ σ.support.image markedMemoryPotentialOperation)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ
      (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhase σ θ t)) f =
        markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f := by
  have hmod (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
      markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhase σ θ t) s c = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact markedMemoryEdgeBirthPhase_eq_one σ θ t ht j _
  unfold markedRawEdgeModifiedSymmetrized markedRawEdgeSymmetrized
  congr 1
  funext s
  unfold markedRawEdgeModifiedApply markedRawEdgeApply
  apply Finset.sum_congr rfl
  intro c _
  rw [hmod,one_mul]

end ArtinMatthews
