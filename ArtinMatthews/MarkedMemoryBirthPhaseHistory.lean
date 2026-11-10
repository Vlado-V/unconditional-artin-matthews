module

public import ArtinMatthews.MarkedMemoryBirthModifiedEdgeSum
public import ArtinMatthews.MarkedMemoryBirthPhaseWord
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

/-! Literal finite chronological histories of the oriented local-phase
word. Geometric reversal affects only its physical kernel. All actual
ghost choices, fresh/performed flags and both slot permutations remain. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryBirthPhaseEdgeWeight
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ))
    (j : ℕ) (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  if orientation j then markedMemoryEdgeBirthModifiedWeight ν V hZ (markedRawEdgeAdjointCutoff ψ)
    (fun u => star (η u)) d₀ Y Q ρ (fun u => star (χ j u)) (markedMemoryEdgeBirthPhaseAt σ θ j) s c
  else markedMemoryEdgeBirthModifiedWeight ν V hZ ψ η d₀ Y Q ρ (χ j) (markedMemoryEdgeBirthPhaseAt σ θ j) s c

theorem markedMemoryBirthPhaseEdgeWeight_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (j : ℕ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ c : MarkedMemoryEdgeChoice hZ s,
      markedMemoryBirthPhaseEdgeWeight ν V hZ ψ η d₀ Y Q ρ orientation χ σ θ j s c*
        f (markedMemoryEdgeChoiceTarget hZ s c)) =
      (if orientation j then markedRawEdgeModifiedSymmetrized ν V hZ (markedRawEdgeAdjointCutoff ψ)
        (fun u => star (η u)) d₀ Y Q ρ (fun u => star (χ j u))
        (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j))
      else markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ (χ j)
        (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j))) f s := by
  by_cases hj : orientation j
  · simp only [markedMemoryBirthPhaseEdgeWeight,ite_eq_left hj]
    exact markedMemoryEdgeBirthModifiedChoice_sum ν V hZ _ _ d₀ Y Q ρ _ _ f s
  · simp only [markedMemoryBirthPhaseEdgeWeight,ite_eq_right hj]
    exact markedMemoryEdgeBirthModifiedChoice_sum ν V hZ _ _ d₀ Y Q ρ _ _ f s

def markedMemoryBirthPhaseHistoryWeight
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,s,h => markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h *
      markedMemoryGhostBirthPhaseAt σ θ j h.sizes.1 h.births
  | n+1,j,s,h => markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1 *
      markedMemoryGhostBirthPhaseAt σ θ j h.1.sizes.1 h.1.births *
      markedMemoryBirthPhaseEdgeWeight ν V hZ ψ η d₀ Y Q ρ orientation χ σ θ j
        (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 *
      markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ n (j+1) h.2.2

theorem markedMemoryBirthPhaseHistory_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ))
    (f : MarkedRawState P (pads+1) B Z → ℂ) (n j : ℕ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ h : MarkedMemoryChronologicalHistory hZ n s,
      markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ n j h *
        f (markedMemoryChronologicalTarget hZ h)) =
      markedMemoryBirthPhaseWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ n j f s := by
  classical
  induction n generalizing j s with
  | zero =>
    unfold markedMemoryBirthPhaseHistoryWeight markedMemoryBirthPhaseWord markedOperatorWord
      markedRawGhostBirthModifiedApply markedRawGhostModifiedApply
    apply Finset.sum_congr rfl
    intro h _
    simp only [markedMemoryChronologicalTarget]
    ring
  | succ n ih =>
    change (∑ h : Σ ghost : MarkedMemoryGhostChoice hZ s,
        Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
          MarkedMemoryChronologicalHistory hZ n
            (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge),
      markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ (n+1) j h *
        f (markedMemoryChronologicalTarget hZ (n := n+1) h)) = _
    simp only [Fintype.sum_sigma,markedMemoryBirthPhaseHistoryWeight,markedMemoryChronologicalTarget]
    simp_rw [mul_assoc,← Finset.mul_sum,ih]
    simp_rw [← Fintype.sum_sigma']
    simp_rw [markedMemoryBirthPhaseEdgeWeight_sum]
    change (∑ ghost : MarkedMemoryGhostChoice hZ s,
      markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s ghost *
        (markedMemoryGhostBirthPhaseAt σ θ j ghost.sizes.1 ghost.births * _)) = _
    rfl

end ArtinMatthews
