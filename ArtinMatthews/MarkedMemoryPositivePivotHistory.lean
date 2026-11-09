module

public import ArtinMatthews.MarkedMemoryPositivePivotWord
public import ArtinMatthews.MarkedMemoryBirthEventBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite history expansion of the positive conditional word.
The memo is updated by each literal birth tuple; no historical guard is
replaced by a function of the physical state alone. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryPositivePivotHistoryWeight
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N)) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s →
      (MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) → ℝ
  | 0,j,s,h,old => if hg : j<N+1 then
      if markedMemoryGhostPivotGate σ ⟨j,hg⟩ old h.sizes.1 h.births then
        ‖markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h‖ else 0
    else 0
  | n+1,j,s,h,old => if hg : j<N+1 then
      if markedMemoryGhostPivotGate σ ⟨j,hg⟩ old h.1.sizes.1 h.1.births then
        if he : j<N then
          let afterGhost := markedMemoryGhostPivotValues ⟨j,hg⟩ old h.1.sizes.1 h.1.births
          let source := markedRawSlotEquiv h.2.1.1 (markedMemoryGhostChoiceTarget hZ s h.1)
          if markedMemoryEdgePivotGate σ ⟨j,he⟩ afterGhost hZ source h.2.1.2.1 then
            ‖markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1‖*
              ‖markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation χ j
                (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1‖*
              markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ n (j+1) h.2.2
                (markedMemoryEdgePivotValues ⟨j,he⟩ afterGhost hZ source h.2.1.2.1)
          else 0
        else 0
      else 0
    else 0

theorem markedMemoryPositivePivotHistoryWeight_nonneg
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (old : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) :
    0 ≤ markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ n j h old := by
  induction n generalizing j s old with
  | zero =>
    unfold markedMemoryPositivePivotHistoryWeight
    split_ifs <;> positivity
  | succ n ih =>
    unfold markedMemoryPositivePivotHistoryWeight
    dsimp only
    split_ifs
    · exact mul_nonneg
        (mul_nonneg (norm_nonneg (markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1))
          (norm_nonneg (markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation χ j
            (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1))) (ih (j+1) h.2.2 _)
    all_goals exact le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryPositivePivotHistory_sum
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (f : MarkedRawState P (pads+1) B Z → ℝ) (n j : ℕ)
    (s : MarkedRawState P (pads+1) B Z)
    (old : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes) :
    (∑ h : MarkedMemoryChronologicalHistory hZ n s,
      markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ n j h old*
        f (markedMemoryChronologicalTarget hZ h)) =
      markedMemoryPositivePivotWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ n j (fun _ => f) old s := by
  classical
  induction n generalizing j s old with
  | zero =>
    by_cases hg : j<N+1
    · simp only [markedMemoryPositivePivotHistoryWeight,dite_eq_left hg,markedMemoryPositivePivotWord,
        markedConditionalWord,markedMemoryPositiveGhostPivotAt,markedMemoryPositiveGhostPivot,
        markedMemoryChronologicalTarget]
      apply Finset.sum_congr rfl
      intro h _
      split_ifs <;> simp only [zero_mul]
    · simp only [markedMemoryPositivePivotHistoryWeight,dite_eq_right hg,zero_mul,Finset.sum_const_zero,
        markedMemoryPositivePivotWord,markedConditionalWord,markedMemoryPositiveGhostPivotAt]
  | succ n ih =>
    change (∑ h : Σ ghost : MarkedMemoryGhostChoice hZ s,
        Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
          MarkedMemoryChronologicalHistory hZ n
            (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge),
      markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ (n+1) j h old*
        f (markedMemoryChronologicalTarget hZ (n := n+1) h)) = _
    simp only [Fintype.sum_sigma,markedMemoryPositivePivotHistoryWeight,markedMemoryChronologicalTarget]
    by_cases hg : j<N+1
    · simp only [dite_eq_left hg]
      by_cases he : j<N
      · simp only [dite_eq_left he]
        unfold markedMemoryPositivePivotWord
        simp only [markedConditionalWord,markedMemoryPositiveGhostPivotAt,dite_eq_left hg,
          markedMemoryPositiveGhostPivot,markedMemoryPositiveEdgePivotAt,dite_eq_left he]
        apply Finset.sum_congr rfl
        intro ghost _
        by_cases hghost : markedMemoryGhostPivotGate σ ⟨j,hg⟩ old ghost.sizes.1 ghost.births
        · simp only [ite_eq_left hghost]
          by_cases ho : orientation j
          · simp only [ite_eq_left ho,markedMemoryPositiveEdgePivot]
            rw [Finset.mul_sum]
            conv_rhs => rw [Fintype.sum_sigma]
            apply Finset.sum_congr rfl
            intro sourceSlots _
            apply Finset.sum_congr rfl
            intro edge _
            split_ifs
            · simp only [markedMemoryGeometricEdgeChoiceWeight,ite_eq_left ho]
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum,← Finset.mul_sum,ih]
              rfl
            · simp only [zero_mul,Finset.sum_const_zero,mul_zero]
          · simp only [ite_eq_right ho,markedMemoryPositiveEdgePivot]
            rw [Finset.mul_sum]
            conv_rhs => rw [Fintype.sum_sigma]
            apply Finset.sum_congr rfl
            intro sourceSlots _
            apply Finset.sum_congr rfl
            intro edge _
            split_ifs
            · simp only [markedMemoryGeometricEdgeChoiceWeight,ite_eq_right ho]
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum,← Finset.mul_sum,ih]
              rfl
            · simp only [zero_mul,Finset.sum_const_zero,mul_zero]
        · simp only [ite_eq_right hghost,zero_mul,Finset.sum_const_zero]
      · simp only [dite_eq_right he,ite_self,zero_mul,Finset.sum_const_zero,
          markedMemoryPositivePivotWord,markedConditionalWord,markedMemoryPositiveGhostPivotAt,
          dite_eq_left hg,markedMemoryPositiveGhostPivot,markedMemoryPositiveEdgePivotAt,mul_zero]
    · simp only [dite_eq_right hg,zero_mul,Finset.sum_const_zero,
        markedMemoryPositivePivotWord,markedConditionalWord,markedMemoryPositiveGhostPivotAt]

end ArtinMatthews
