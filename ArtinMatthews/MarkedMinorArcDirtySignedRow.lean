module

public import ArtinMatthews.MarkedMinorArcDirtyMajorChoiceWeighted
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeWeight
public import ArtinMatthews.MarkedMinorArcDirtyMajorSupport
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgePromotionBound
public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeSlotGeometry
public import ArtinMatthews.MarkedMinorArcRawCleanSupport
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

/-! The full signed minor row on a fixed promoted-group set, with every
store pattern and actual source-slot average retained. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

def markedDirtySignedFixedWeightedRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ) : ℝ :=
  ∑ σ : J → Equiv.Perm (Fin (pads+1)),markedDirtySourceSlotWeight pads σ*
    ∑ c : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c.1*
        ‖modifier σ c.1*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖*
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
          markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)

theorem markedDirtySignedFixedWeightedRow_modifier_le
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (hv₀ : 0 < v₀)
    (w : Z → ℤ × ℤ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ)
    {L : ℝ} (hmodifier : ∀ σ c,‖modifier σ c‖ ≤ L) :
    markedDirtySignedFixedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s I modifier ≤
      L*markedDirtySignedFixedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s I (fun _ _ => 1) := by
  classical
  unfold markedDirtySignedFixedWeightedRow
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro σ _
  have hpoint : ∀ c : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c.1*
        ‖modifier σ c.1*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖*
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
          markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2) ≤
      L*(markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c.1*
        ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖*
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
          markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)) := by
    intro c
    have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ (markedRawSlotEquiv σ s) c.1
    have hw : 0 ≤ markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
        markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2 :=
      div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le (markedRawMemorySchurWeight_pos hv₀ _).le
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hmodifier σ c.1) (norm_nonneg _)) hm) hw).trans_eq (by ring)
  simp only [one_mul]
  calc
    _ ≤ markedDirtySourceSlotWeight pads σ*(∑ c,L*(markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c.1*
        ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖*
        (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
          markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun c _ => hpoint c))
        (by unfold markedDirtySourceSlotWeight; positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem markedDirtySignedFixedWeightedRow_le_delta_add_major
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (hv₀ : 0 < v₀)
    (w : Z → ℤ × ℤ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (modifier : (σ : J → Equiv.Perm (Fin (pads+1))) → MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) → ℂ)
    (hmodifier : ∀ σ c,‖modifier σ c‖ ≤ 1) :
    markedDirtySignedFixedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s I modifier ≤
      markedDirtyRawEdgeDeltaWeightedRow ν V hZ ψ η d₀ Y ρ v₀
        (markedRawFirstGoodCutoff r d₀ Y w χ) s I+
      markedDirtyMajorSymWeightedRow ν V hZ η ψ r d₀ Y Q ρ v₀ w χ s I := by
  classical
  unfold markedDirtySignedFixedWeightedRow markedDirtyRawEdgeDeltaWeightedRow
    markedDirtyMajorSymWeightedRow markedDirtyMajorChoiceWeightedRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  rw [← mul_add,← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by unfold markedDirtySourceSlotWeight; positivity)
  apply Finset.sum_le_sum
  intro c _
  have hm := markedDirtyRawEdge_prime_mass_nonneg ν V hν hV hZ (markedRawSlotEquiv σ s) c.1
  have hwgt : 0 ≤ markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c.1)/
      markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2 :=
    div_nonneg (markedRawMemorySchurWeight_pos hv₀ _).le (markedRawMemorySchurWeight_pos hv₀ _).le
  have hn : ‖modifier σ c.1*markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
      (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖ ≤
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
        (markedRawEdgeDeltaDetector ψ Y) (markedRawSlotEquiv σ s) c.1‖+
      ‖markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ (markedRawFirstGoodCutoff r d₀ Y w χ)
        (markedRawEdgeMajorDetector ψ Q Y) (markedRawSlotEquiv σ s) c.1‖ := by
    calc
      _ ≤ ‖markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ
          (markedRawFirstGoodCutoff r d₀ Y w χ) (markedRawSlotEquiv σ s) c.1‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (hmodifier σ c.1)
      _ ≤ _ := by
        rw [markedRawEdgeChoiceCoefficient_delta_sub_major]
        exact norm_sub_le _ _
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hm) hwgt).trans_eq (by ring)

theorem markedRawEdgeDetectorCoefficient_eq_zero_of_source_zero
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (η : ℝ → ℂ) (d₀ Y ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (detector : ℤ → ℤ → ℤ → ℂ) (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) (hs : χ s=0) :
    markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ detector s c=0 := by
  by_contra hn
  have hh := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ detector s c hn
  exact (markedRawEndpointFactor_ne_zero_test hZ 1 χ s hh.2.2.2.1) hs

theorem markedDirtyDeltaWeightedRow_eq_zero_of_source_zero
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (hs : ∀ σ : J → Equiv.Perm (Fin (pads+1)),χ (markedRawSlotEquiv σ s)=0) :
    markedDirtyRawEdgeDeltaWeightedRow ν V hZ ψ η d₀ Y ρ v₀ χ s I=0 := by
  classical
  unfold markedDirtyRawEdgeDeltaWeightedRow
  apply Finset.sum_eq_zero
  intro σ _
  have hz : ∀ c : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
        (markedRawSlotEquiv σ s) c.1=0 := fun c =>
    markedRawEdgeDetectorCoefficient_eq_zero_of_source_zero hZ η d₀ Y ρ χ _ _ c.1 (hs σ)
  simp only [hz,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero]

theorem markedDirtyDeltaWeightedRow_eq_zero_of_not_distinct
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ η : ℝ → ℂ) (d₀ Y ρ v₀ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (I : Finset J)
    (hs : ¬∀ j,Function.Injective (s.2.1 j)) :
    markedDirtyRawEdgeDeltaWeightedRow ν V hZ ψ η d₀ Y ρ v₀ χ s I=0 := by
  classical
  unfold markedDirtyRawEdgeDeltaWeightedRow
  apply Finset.sum_eq_zero
  intro σ _
  have hz : ∀ c : MarkedDirtyFixedEdgeChoice hZ (markedRawSlotEquiv σ s) I,
      markedRawEdgeChoiceDetectorCoefficient hZ η d₀ Y ρ χ (markedRawEdgeDeltaDetector ψ Y)
        (markedRawSlotEquiv σ s) c.1=0 := by
    intro c
    by_contra hn
    have hh := markedRawEdgeChoiceDetectorCoefficient_support hZ η d₀ Y ρ χ _ _ c.1 hn
    have hd := markedRawEndpointFactor_ne_zero_distinct hZ 1 χ (markedRawSlotEquiv σ s) hh.2.2.2.1
    exact hs ((markedDirtyRawStateSlot_distinct_iff σ s).mp hd)
  simp only [hz,norm_zero,mul_zero,zero_mul,Finset.sum_const_zero]

end
end ArtinMatthews
