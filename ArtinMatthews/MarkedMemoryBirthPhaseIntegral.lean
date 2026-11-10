module

public import ArtinMatthews.MarkedMemoryHistoryPhaseFactor
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Circle orthogonality on the original oriented history coefficient.
The finite performed-birth event is recovered exactly, with no absolute
value taken before the signed history sum. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedBirthValuePhase_continuous (p : Option Nat.Primes) :
    Continuous (fun θ : AddCircle (1:ℝ) => markedBirthValuePhase θ p) := by
  cases p with
  | none => exact continuous_const
  | some p => exact (fourier (p.1:ℤ)).continuous

theorem markedBirthLocalMultiplier_continuous {A : Type*} [Fintype A] [DecidableEq A]
    (σ : Equiv.Perm A) (a : A) (p : Option Nat.Primes) :
    Continuous (fun θ : A → AddCircle (1:ℝ) => markedBirthLocalMultiplier σ θ a p) := by
  unfold markedBirthLocalMultiplier
  by_cases ha : a ∈ σ.support
  · simp only [ha,ite_true]
    exact ((markedBirthValuePhase_continuous p).comp (continuous_apply (σ.symm a))).mul
      (((markedBirthValuePhase_continuous p).comp (continuous_apply a)).star)
  · simp only [ha,ite_false]
    exact continuous_const

theorem markedMemoryBirthLocalProduct_continuous
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ N s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) :
    Continuous (fun θ => markedMemoryBirthLocalProduct hZ h σ θ) := by
  unfold markedMemoryBirthLocalProduct
  exact continuous_finsetProd _ (fun a _ => markedBirthLocalMultiplier_continuous σ a _)

theorem markedMemoryBirthLocalProduct_integrable
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ N s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) :
    Integrable (fun θ => markedMemoryBirthLocalProduct hZ h σ θ)
      (Measure.pi (fun _ => AddCircle.haarAddCircle)) :=
  (markedMemoryBirthLocalProduct_continuous hZ h σ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem markedMemoryBirthPhaseHistory_initial_factor
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ))
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ N s) :
    markedMemoryBirthInitialPhase σ θ s *
      markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ N 0 h =
    markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ N 0 h *
      markedMemoryBirthLocalProduct hZ h σ θ := by
  rw [markedMemoryBirthPhaseHistoryWeight_factor,markedMemoryBirthLocalProduct_eq_initial_history]
  ring

theorem markedMemoryBirthPhaseHistory_event_integral
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ N s) :
    (∫ θ, markedMemoryBirthInitialPhase σ θ s *
      markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ N 0 h
        ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) =
      if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then
        markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ N 0 h else 0 := by
  simp_rw [markedMemoryBirthPhaseHistory_initial_factor]
  rw [integral_const_mul,markedMemoryBirthLocalProduct_integral]
  split_ifs <;> simp only [mul_one,mul_zero]

end ArtinMatthews
