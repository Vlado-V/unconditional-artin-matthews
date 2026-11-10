module

public import ArtinMatthews.MarkedMemoryHistoryBirths
public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor
public import ArtinMatthews.MarkedMemoryBirthDistinctWeighted
public import ArtinMatthews.MarkedMemoryBirthPhaseIntegral
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

/-! Exact oriented history sums for one equality event and for the
original global performed-birth distinctness guard. Circle averaging is
performed after the signed finite history sum. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

local instance birthEventPotentialPermFintype {J : Type*} [Fintype J] [DecidableEq J] (M B N : ℕ) :
    Fintype (Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) :=
  @Equiv.instFintype (MarkedMemoryPotentialAddress J M B N)
    (MarkedMemoryPotentialAddress J M B N) inferInstance inferInstance inferInstance inferInstance

def markedMemoryGeometricBoundaryHistoryTerm
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (z₀ : Z)
    (s : MarkedRawState P (pads+1) B Z) (h : MarkedMemoryChronologicalHistory hZ N s) : ℂ :=
  (markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ N 0 h *
      markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ h)

def markedMemoryBirthEventBoundaryPairing
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z) : ℂ :=
  ∑ s, ∑ h : MarkedMemoryChronologicalHistory hZ N s,
    if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then
      markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h else 0

def markedMemoryBirthDistinctGeometricBoundaryPairing
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (z₀ : Z) : ℂ :=
  ∑ s, ∑ h : MarkedMemoryChronologicalHistory hZ N s,
    if MarkedMemoryHistoryBirthDistinct hZ h then
      markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h else 0

theorem markedMemoryBirthDistinctGeometricBoundary_eq_permutation_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (z₀ : Z) :
    markedMemoryBirthDistinctGeometricBoundaryPairing (N := N) ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ =
      ∑ σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N), ((σ.sign:ℤ):ℂ)*
        markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ :=
  markedMemoryHistoryBirthDistinct_boundary_permutation_sum hZ
    (markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀)

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthPhaseBoundary_eq_history_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (z₀ : Z) :
    markedMemoryBirthPhaseBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ z₀ =
      ∑ s, ∑ h : MarkedMemoryChronologicalHistory hZ N s,
        markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h *
          markedMemoryBirthLocalProduct hZ h σ θ := by
  unfold markedMemoryBirthPhaseBoundaryPairing
  apply Finset.sum_congr rfl
  intro s _
  rw [← markedMemoryBirthPhaseHistory_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  calc
    _ = ((markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*
        markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ h)) *
        (markedMemoryBirthInitialPhase σ θ s *
          markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ N 0 h) := by ring
    _ = _ := by rw [markedMemoryBirthPhaseHistory_initial_factor]; unfold markedMemoryGeometricBoundaryHistoryTerm; ring

theorem markedMemoryBirthEventBoundary_eq_integral
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z) :
    markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ =
      ∫ θ, markedMemoryBirthPhaseBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ z₀
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle) := by
  simp_rw [markedMemoryBirthPhaseBoundary_eq_history_sum]
  have hi (s : MarkedRawState P (pads+1) B Z) (h : MarkedMemoryChronologicalHistory hZ N s) :
      Integrable (fun θ => markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h *
        markedMemoryBirthLocalProduct hZ h σ θ) (Measure.pi (fun _ => AddCircle.haarAddCircle)) :=
    (markedMemoryBirthLocalProduct_integrable hZ h σ).const_mul _
  rw [integral_finsetSum _ (fun s _ => integrable_finsetSum _ (fun h _ => hi s h))]
  apply Finset.sum_congr rfl
  intro s _
  rw [integral_finsetSum _ (fun h _ => hi s h)]
  apply Finset.sum_congr rfl
  intro h _
  rw [integral_const_mul,markedMemoryBirthLocalProduct_integral]
  split_ifs <;> simp only [mul_one,mul_zero]

end ArtinMatthews
