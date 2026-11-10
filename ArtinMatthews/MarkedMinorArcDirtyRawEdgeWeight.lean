module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeRow
public import ArtinMatthews.MarkedMinorArcRawGhostWeight
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
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

/-! Actual edge Schur-weight transport costs only v0^K, never a factor
depending on memory cutoff or the large parameter. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

theorem markedDirtyRawEdge_target_weight_ratio_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) {v₀ : ℝ} (hv₀ : 1 ≤ v₀) :
    markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ s choice)/markedRawMemorySchurWeight v₀ s.2.2 ≤
      v₀^(Fintype.card J) := by
  have hvpos : 0 < v₀ := lt_of_lt_of_le zero_lt_one hv₀
  rw [markedRawEdgeTargetMemory,markedRawGhost_target_weight_ratio hvpos.ne']
  calc
    _ ≤ ∏ _j : J, v₀ := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact div_nonneg (pow_nonneg hvpos.le _) (pow_nonneg hvpos.le _)
      · intro j _
        have hl : ((markedRawEdgeStoreSizes hZ s choice).1 j:ℕ) ≤ 1 := by
          change (if choice.store j then 1 else 0) ≤ 1
          split_ifs <;> omega
        calc
          _ ≤ v₀^((markedRawEdgeStoreSizes hZ s choice).1 j:ℕ)/1 :=
            div_le_div_of_nonneg_left (pow_nonneg hvpos.le _) zero_lt_one (one_le_pow₀ hv₀)
          _ ≤ v₀ := by
            rw [div_one]
            simpa only [pow_one] using pow_le_pow_right₀ hv₀ hl
    _ = _ := by simp

def markedDirtyRawEdgeDeltaWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) : ℝ := by
  classical
  exact ∑ σ : J → Equiv.Perm (Fin (pads+1)), markedDirtySourceSlotWeight pads σ *
    ∑ choice : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 *
        ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
          (markedRawSlotEquiv σ s) choice.1‖ *
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) choice.1)/
          markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)

theorem markedDirtyRawEdge_delta_weighted_row_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p, 0 ≤ ν j p) (hV : ∀ j, 0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ) (hv₀ : 1 ≤ v₀) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J) :
    markedDirtyRawEdgeDeltaWeightedRow ν V hZ ψ η d₀ Y ρ v₀ χ s I ≤
      v₀^(Fintype.card J)*markedDirtyRawEdgeDeltaRow ν V hZ ψ η d₀ Y ρ χ s I := by
  classical
  unfold markedDirtyRawEdgeDeltaWeightedRow markedDirtyRawEdgeDeltaRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hw : 0 ≤ markedDirtySourceSlotWeight pads σ := by unfold markedDirtySourceSlotWeight; positivity
  calc
    _ ≤ markedDirtySourceSlotWeight pads σ *
        ∑ choice : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
          (markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) choice.1 *
            ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
              (markedRawSlotEquiv σ s) choice.1‖)*v₀^(Fintype.card J) := by
      apply mul_le_mul_of_nonneg_left _ hw
      apply Finset.sum_le_sum
      intro choice _
      exact mul_le_mul_of_nonneg_left
        (markedDirtyRawEdge_target_weight_ratio_le hZ (markedRawSlotEquiv σ s) choice.1 hv₀)
        (mul_nonneg (markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ (markedRawSlotEquiv σ s) choice.1)
          (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

end ArtinMatthews
