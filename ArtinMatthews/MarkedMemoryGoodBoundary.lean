module

public import ArtinMatthews.MarkedMemoryGoodCutoff
public import ArtinMatthews.MarkedRawBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! Source-first bad insertion for the true chronological boundary
pairing. Cauchy keeps the actual propagated error energy explicit. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedMemoryFirstBadContribution_step
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ (n+1) s) :
    let u := markedMemoryGhostChoiceTarget hZ s h.1
    let source := markedRawSlotEquiv h.2.1.1 u
    let target := markedRawEdgeTargetState hZ source h.2.1.2.1
    let W := markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ (n+1) j h
    markedMemoryFirstBadContribution ν V hZ ψ η d₀ Y Q ρ qStage χ G (n+1) j h =
      (if ¬G j source then W else 0) + (if G j source ∧ ¬G j target then W else 0) +
        (if G j source ∧ G j target then
          markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1 *
            markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (χ j) u h.2.1 *
            markedMemoryFirstBadContribution ν V hZ ψ η d₀ Y Q ρ qStage χ G n (j+1) h.2.2 else 0) := by
  dsimp only
  conv_lhs => rw [markedMemoryFirstBadContribution]
  unfold MarkedMemoryEdgeGood
  by_cases hs : G j (markedRawSlotEquiv h.2.1.1 (markedMemoryGhostChoiceTarget hZ s h.1)) <;>
    by_cases ht : G j (markedRawEdgeTargetState hZ
      (markedRawSlotEquiv h.2.1.1 (markedMemoryGhostChoiceTarget hZ s h.1)) h.2.1.2.1) <;>
    simp [hs,ht]

def markedMemoryFirstBadApply
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop)
    (n j : ℕ) (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) : ℂ :=
  ∑ h : MarkedMemoryChronologicalHistory hZ n s,
    markedMemoryFirstBadContribution ν V hZ ψ η d₀ Y Q ρ qStage χ G n j h *
      f (markedMemoryChronologicalTarget hZ h)

theorem markedMemoryChronologicalApply_first_bad
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop)
    (n j : ℕ) (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j f s -
      markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage
        (fun i u => if G i u then χ i u else 0) n j f s =
      markedMemoryFirstBadApply ν V hZ ψ η d₀ Y Q ρ qStage χ G n j f s := by
  rw [← markedMemoryChronological_sum,← markedMemoryChronological_sum,← Finset.sum_sub_distrib]
  unfold markedMemoryFirstBadApply
  apply Finset.sum_congr rfl
  intro h _
  rw [← sub_mul,markedMemoryChronologicalWeight_first_bad]

def markedMemoryBoundaryPairing
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (n j : ℕ) (z₀ : Z) : ℂ :=
  ∑ s, (markedRawStateMass ν s:ℂ) * star (markedRawBoundary z₀ s) *
    markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j (markedRawBoundary z₀) s

theorem markedMemoryBoundaryPairing_first_bad
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop) (n j : ℕ) (z₀ : Z) :
    markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage χ n j z₀ -
      markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage
        (fun i u => if G i u then χ i u else 0) n j z₀ =
      ∑ s,(markedRawStateMass ν s:ℂ)*star (markedRawBoundary z₀ s)*
        markedMemoryFirstBadApply ν V hZ ψ η d₀ Y Q ρ qStage χ G n j (markedRawBoundary z₀) s := by
  unfold markedMemoryBoundaryPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [← mul_sub,markedMemoryChronologicalApply_first_bad]

theorem markedWeightedBoundary_cauchy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s,0 ≤ μ s) (f g : Ω → ℂ) :
    ‖∑ s,(μ s:ℂ)*star (f s)*g s‖^2 ≤
      (∑ s,μ s*‖f s‖^2)*(∑ s,μ s*‖g s‖^2) := by
  have hn : ‖∑ s,(μ s:ℂ)*star (f s)*g s‖ ≤ ∑ s,μ s*‖f s‖*‖g s‖ := by
    have h := norm_sum_le Finset.univ (fun s => (μ s:ℂ)*star (f s)*g s)
    simpa only [norm_mul,norm_star,Complex.norm_real,Real.norm_of_nonneg (hμ _)] using h
  apply (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (hμ s) (sq_nonneg _)
  · intro s _
    exact mul_nonneg (hμ s) (sq_nonneg _)
  · intro s _
    exact le_of_eq (by ring)

theorem markedMemoryBoundaryPairing_first_bad_cauchy
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (hν : ∀ j p,0 ≤ ν j p) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (G : ℕ → MarkedRawState P (pads+1) B Z → Prop) (n j : ℕ) (z₀ : Z) :
    ‖markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage χ n j z₀ -
      markedMemoryBoundaryPairing ν V hZ ψ η d₀ Y Q ρ qStage
        (fun i u => if G i u then χ i u else 0) n j z₀‖^2 ≤
      markedRawBoundaryEnergy ν (pads+1) B z₀ *
        ∑ s,markedRawStateMass ν s *
          ‖markedMemoryFirstBadApply ν V hZ ψ η d₀ Y Q ρ qStage χ G n j (markedRawBoundary z₀) s‖^2 := by
  rw [markedMemoryBoundaryPairing_first_bad]
  exact markedWeightedBoundary_cauchy (markedRawStateMass ν) (markedRawStateMass_nonneg ν hν)
    (markedRawBoundary z₀) _

end
end ArtinMatthews
