module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceRow
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeOmissionAverage
public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight
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

/-! True v0 memory-Schur weights and the actual source-slot average of
major comparison rows. The only weight loss is the fixed v0^K. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedDirtyMajorChoiceWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ := by
  classical
  exact ∑ choice : MarkedDirtyFixedEdgeChoice hZ s I,
    markedRawEdgeChoicePrimeMass ν V hZ s choice.1 *
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ
        (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawEdgeMajorDetector ψ Q Y) s choice.1‖ *
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice.1)/markedRawMemorySchurWeight v₀ s.2.2)

def markedDirtyMajorSymWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ :=
  ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ *
    markedDirtyMajorChoiceWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ (markedRawSlotEquiv σ s) I

theorem markedDirtyMajorChoiceWeightedRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (η ψ : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J) :
    markedDirtyMajorChoiceWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ s I ≤
      v₀^(Fintype.card J)*markedDirtyMajorChoiceRow ν V hZ η ψ r d₀ Y Q ρ w χ s I := by
  classical
  unfold markedDirtyMajorChoiceWeightedRow markedDirtyMajorChoiceRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro choice _
  exact (mul_le_mul_of_nonneg_left (markedDirtyRawEdge_target_weight_ratio_le hZ s choice.1 hv₀)
    (mul_nonneg (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ s choice.1) (norm_nonneg _))).trans_eq
      (by ring)

theorem markedDirtySourceSlotWeight_total {J : Type*} [Fintype J] [DecidableEq J] (pads : ℕ) :
    (∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ)=1 := by
  have hh := markedDirtySourceOmission_expectation pads (Fin.last pads) (fun _ : J → Fin (pads+1) => (1:ℝ))
  simp only [mul_one] at hh
  exact hh.trans (markedUniformOmissionWeight_total (Nat.succ_pos pads))

end ArtinMatthews
