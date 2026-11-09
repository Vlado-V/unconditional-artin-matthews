module

public import ArtinMatthews.MarkedMemoryHistoryChronological
public import ArtinMatthews.MarkedMinorArcRawEdgeDirtyPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Exact cutoff insertion on actual dependent chronological histories.
The good tests are evaluated at the literal two edge endpoints before the
destination slot permutation; no history or index multiplicity is changed. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdgeChoiceCoefficient_cutoff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (G : MarkedRawState P (pads+1) B Z → Prop)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ (fun u => if G u then χ u else 0) s c =
      if G s ∧ G (markedRawEdgeTargetState hZ s c) then
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ s c else 0 := by
  rw [markedRawEdgeChoiceCoefficient_eq_joint,markedRawEdgeJointCoefficient_eq_detector,
    markedRawEdgeJointDetectorCoefficient_cutoff]
  split_ifs
  · rw [markedRawEdgeChoiceCoefficient_eq_joint,markedRawEdgeJointCoefficient_eq_detector]
  · rfl

def MarkedMemoryEdgeGood {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (G : MarkedRawState P (pads+1) B Z → Prop)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) : Prop :=
  G (markedRawSlotEquiv c.1 s) ∧
    G (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2.1)

theorem markedMemoryEdgeChoiceWeight_cutoff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (G : MarkedRawState P (pads+1) B Z → Prop)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (fun u => if G u then χ u else 0) s c =
      if MarkedMemoryEdgeGood hZ G s c then markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c else 0 := by
  unfold markedMemoryEdgeChoiceWeight
  rw [markedRawEdgeChoiceCoefficient_cutoff]
  unfold MarkedMemoryEdgeGood
  split_ifs <;> simp

def MarkedMemoryHistoryGood {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → Prop
  | 0,_,_,_ => True
  | n+1,j,s,h =>
      MarkedMemoryEdgeGood hZ (G j) (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 ∧
        MarkedMemoryHistoryGood hZ G n (j+1) h.2.2

theorem markedMemoryChronologicalWeight_good_cutoff
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage
      (fun i u => if G i u then χ i u else 0) n j h =
      if MarkedMemoryHistoryGood hZ G n j h then
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h else 0 := by
  induction n generalizing j s with
  | zero => simp [markedMemoryChronologicalWeight,MarkedMemoryHistoryGood]
  | succ n ih =>
    rw [markedMemoryChronologicalWeight,markedMemoryChronologicalWeight,
      markedMemoryEdgeChoiceWeight_cutoff,ih]
    simp only [MarkedMemoryHistoryGood]
    by_cases he : MarkedMemoryEdgeGood hZ (G j) (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 <;>
      by_cases ht : MarkedMemoryHistoryGood hZ G n (j+1) h.2.2 <;> simp [he,ht]

def markedMemoryFirstBadContribution {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,_,_,_ => 0
  | n+1,j,s,h =>
      if MarkedMemoryEdgeGood hZ (G j) (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 then
        markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1 *
          markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (χ j)
            (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 *
          markedMemoryFirstBadContribution ν V hZ ψ η d₀ Y Q ρ qStage χ G n (j+1) h.2.2
      else markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ (n+1) j h

theorem markedMemoryChronologicalWeight_first_bad
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j h -
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage
        (fun i u => if G i u then χ i u else 0) n j h =
      markedMemoryFirstBadContribution ν V hZ ψ η d₀ Y Q ρ qStage χ G n j h := by
  induction n generalizing j s with
  | zero => simp [markedMemoryFirstBadContribution,markedMemoryChronologicalWeight]
  | succ n ih =>
    rw [markedMemoryChronologicalWeight,markedMemoryChronologicalWeight,
      markedMemoryEdgeChoiceWeight_cutoff]
    by_cases he : MarkedMemoryEdgeGood hZ (G j) (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1
    · rw [ite_eq_left he]
      rw [← mul_sub,ih]
      exact (ite_eq_left he).symm
    · rw [ite_eq_right he]
      simp only [mul_zero,zero_mul,sub_zero]
      exact (ite_eq_right he).symm

end
end ArtinMatthews
