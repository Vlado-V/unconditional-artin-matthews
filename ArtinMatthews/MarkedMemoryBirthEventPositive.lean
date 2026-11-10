module

public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedMemoryInitialPivotMass
public import ArtinMatthews.MarkedMemoryPivotCompatible
public import ArtinMatthews.MarkedMemoryPositivePivotWord
public import ArtinMatthews.MarkedMemoryPositivePivotCompatible
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
public import Mathlib.Tactic.Monotonicity.Lemmas
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
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! Finite domination of an original permutation-event boundary by the
positive conditional word. The two compatibility premises are purely
literal history facts, discharged by the chronological memo packet. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryPositivePivotBoundary
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z) : ℝ :=
  ∑ s : MarkedRawState P (pads+1) B Z,markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*
    (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then
      markedMemoryPositivePivotWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0
        (fun _ t => ‖markedRawBoundary z₀ t‖) (markedMemoryInitialPivotValues (fun _ => none) s.2.1) s
    else 0)

theorem markedMemoryPositivePivotBoundary_le
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z)
    (v₀ C S : ℝ) (hC : 0 ≤ C)
    (hword : ∀ old s,markedMemoryPositivePivotWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0
      (fun _ t => ‖markedRawBoundary z₀ t‖) old s ≤ C*markedRawMemorySchurWeight v₀ s.2.2)
    (hsource : (∑ s : MarkedRawState P (pads+1) B Z,
      markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*markedRawMemorySchurWeight v₀ s.2.2*
        (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then 1 else 0)) ≤ S) :
    markedMemoryPositivePivotBoundary ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ ≤ C*S := by
  unfold markedMemoryPositivePivotBoundary
  calc
    _ ≤ ∑ s : MarkedRawState P (pads+1) B Z,
        C*(markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*markedRawMemorySchurWeight v₀ s.2.2*
          (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro s _
      split_ifs
      · calc
          _ ≤ markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*
              (C*markedRawMemorySchurWeight v₀ s.2.2) :=
            mul_le_mul_of_nonneg_left (hword _ s)
              (mul_nonneg (markedRawStateMass_nonneg ν hν s) (norm_nonneg _))
          _ = _ := by ring
      · simp only [mul_zero]
        exact le_rfl
    _ = C*(∑ s : MarkedRawState P (pads+1) B Z,
        markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*markedRawMemorySchurWeight v₀ s.2.2*
          (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then 1 else 0)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsource hC

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthEventBoundary_le_positive
    {J : Type*} [Fintype J] [decJ : DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (hν : ∀ i p,0 ≤ ν i p) (V : J → ℝ)
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) (z₀ : Z)
    (hinit : ∀ (s : MarkedRawState P (pads+1) B Z) (h : MarkedMemoryChronologicalHistory hZ N s),
      MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ →
        markedMemoryInitialPivotGate σ (fun _ => none) s.2.1)
    (hcompat : ∀ (s : MarkedRawState P (pads+1) B Z) (h : MarkedMemoryChronologicalHistory hZ N s),
      MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ →
        MarkedMemoryPivotCompatible hZ σ N 0 h (markedMemoryInitialPivotValues (fun _ => none) s.2.1)) :
    ‖markedMemoryBirthEventBoundaryPairing ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀‖ ≤
      markedMemoryPositivePivotBoundary ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ z₀ := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  have hpoint (s : MarkedRawState P (pads+1) B Z) (h : MarkedMemoryChronologicalHistory hZ N s) :
      ‖if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then
        markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h else 0‖ ≤
      markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*
        (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then
          markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0 h
            (markedMemoryInitialPivotValues (fun _ => none) s.2.1)*
              ‖markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ h)‖ else 0) := by
    have hmass := markedRawStateMass_nonneg ν hν s
    by_cases he : MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ
    · rw [ite_eq_left he,ite_eq_left (hinit s h he),
        markedMemoryPositivePivotHistoryWeight_of_compatible ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0 h
          (markedMemoryInitialPivotValues (fun _ => none) s.2.1) (hcompat s h he)]
      simp only [markedMemoryGeometricBoundaryHistoryTerm,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hmass,norm_star,mul_assoc,le_refl]
    · rw [ite_eq_right he,norm_zero]
      apply mul_nonneg (mul_nonneg hmass (norm_nonneg _))
      split_ifs
      · exact mul_nonneg
          (markedMemoryPositivePivotHistoryWeight_nonneg ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0 h _)
          (norm_nonneg _)
      · exact le_rfl
  unfold markedMemoryBirthEventBoundaryPairing
  calc
    _ ≤ ∑ s,∑ h : MarkedMemoryChronologicalHistory hZ N s,
        ‖if MarkedBirthPermutationEvent (markedMemoryPotentialAddressValue hZ h) σ then
          markedMemoryGeometricBoundaryHistoryTerm ν V hZ ψ η d₀ Y Q ρ orientation qStage χ z₀ s h else 0‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun s _ => norm_sum_le _ _))
    _ ≤ ∑ s,∑ h : MarkedMemoryChronologicalHistory hZ N s,
        markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*
          (if markedMemoryInitialPivotGate σ (fun _ => none) s.2.1 then
            markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ N 0 h
              (markedMemoryInitialPivotValues (fun _ => none) s.2.1)*
                ‖markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ h)‖ else 0) :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun h _ => hpoint s h))
    _ = _ := by
      unfold markedMemoryPositivePivotBoundary
      apply Finset.sum_congr rfl
      intro s _
      rw [← Finset.mul_sum]
      simp only [Finset.sum_ite_irrel,Finset.sum_const_zero]
      split_ifs
      · exact congrArg (fun a : ℝ => markedRawStateMass ν s*‖markedRawBoundary z₀ s‖*a)
          (markedMemoryPositivePivotHistory_sum ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ
            (fun t => ‖markedRawBoundary z₀ t‖) N 0 s
            (markedMemoryInitialPivotValues (fun _ => none) s.2.1))
      · rfl

end ArtinMatthews
