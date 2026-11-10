module

public import ArtinMatthews.MarkedMemoryHistoryWindow
public import ArtinMatthews.MarkedMemoryBirthEventBoundary
public import ArtinMatthews.MarkedMemoryEdgeWindowSupport
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Actual position-supported endpoint cutoffs kill every chronological
history leaving their window. The zero statement is for the original
signed geometric weight; no norm estimate for an added history test is
assumed. -/

namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)}
  (hW : ∀ z ∈ W, IsCoprime z.1 z.2)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B W → ℂ)

theorem markedMemoryGeometricHistoryWeight_zero_of_not_afterWindow
    (hχ : ∀ j s, s.1.1 ∉ Z → χ j s = 0) (n j : ℕ)
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s)
    (hH : ¬MarkedMemoryHistoryAfterWindow hW Z H) :
    markedMemoryGeometricHistoryWeight ν V hW ψ η d₀ Y Q ρ
      orientation qStage χ n j H = 0 := by
  classical
  induction n generalizing j s with
  | zero => exact False.elim (hH True.intro)
  | succ n ih =>
    by_cases ht : H.2.1.2.1.target.1 ∈ Z
    · have htail : ¬MarkedMemoryHistoryAfterWindow hW Z H.2.2 :=
        fun hrest => hH ⟨ht, hrest⟩
      have hz := ih (j+1) H.2.2 htail
      simp only [markedMemoryGeometricHistoryWeight, hz, mul_zero]
    · have hz := markedMemoryGeometricEdgeChoiceWeight_eq_zero_of_outside hW ν V ψ η
        d₀ Y Q ρ orientation χ Z hχ j (markedMemoryGhostChoiceTarget hW s H.1) H.2.1 ht
      simp only [markedMemoryGeometricHistoryWeight, hz, mul_zero, zero_mul]

theorem markedMemoryGeometricBoundaryTerm_zero_of_not_vertices
    (hχ : ∀ j s, s.1.1 ∉ Z → χ j s = 0) (n : ℕ) (z₀ : W) (hz₀ : z₀.1 ∈ Z)
    (s : MarkedRawState P (pads+1) B W)
    (H : MarkedMemoryChronologicalHistory hW n s)
    (hH : ¬MarkedMemoryHistoryVerticesIn hW Z H) :
    markedMemoryGeometricBoundaryHistoryTerm ν V hW ψ η d₀ Y Q ρ
      orientation qStage χ z₀ s H = 0 := by
  classical
  by_cases hs : s.1.1 ∈ Z
  · have hrest : ¬MarkedMemoryHistoryAfterWindow hW Z H :=
      fun hafter => hH ((markedMemoryHistoryVerticesIn_iff hW H).mpr ⟨hs, hafter⟩)
    have hz := markedMemoryGeometricHistoryWeight_zero_of_not_afterWindow hW ν V ψ η
      d₀ Y Q ρ orientation qStage χ hχ n 0 H hrest
    simp only [markedMemoryGeometricBoundaryHistoryTerm, hz, mul_zero, zero_mul]
  · have hne : s.1 ≠ z₀ := by
      intro heq
      have hp : s.1.1 = z₀.1 := congrArg Subtype.val heq
      exact hs (hp.symm ▸ hz₀)
    simp [markedMemoryGeometricBoundaryHistoryTerm, markedRawBoundary, hne]

theorem markedMemoryGeometricHistoryWeight_zero_of_cutoffs_zero
    (hχ : ∀ j s, χ j s = 0) (n j : ℕ) (hn : 0 < n)
    {s : MarkedRawState P (pads+1) B W}
    (H : MarkedMemoryChronologicalHistory hW n s) :
    markedMemoryGeometricHistoryWeight ν V hW ψ η d₀ Y Q ρ
      orientation qStage χ n j H = 0 := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ hn)
  | succ n =>
    have hz := markedMemoryGeometricEdgeChoiceWeight_eq_zero_of_outside hW ν V ψ η
      d₀ Y Q ρ orientation χ ∅ (fun k t _ => hχ k t) j
      (markedMemoryGhostChoiceTarget hW s H.1) H.2.1 (by simp)
    simp only [markedMemoryGeometricHistoryWeight, hz, mul_zero, zero_mul]

end
end ArtinMatthews
