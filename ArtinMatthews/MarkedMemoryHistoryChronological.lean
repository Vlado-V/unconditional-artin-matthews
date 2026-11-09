module

public import ArtinMatthews.MarkedMemoryHistoryGhostChoice
public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice


set_option backward.privateInPublic true
@[expose] public section

/-! Exact chronological finite histories of the actual forward signed raw
operations G_j E_j ... G_{j+n}. Both slot symmetrizations are included in
 each E choice. The later adjoint and lifespan identifications are separate. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Every node stores the actual dependent choice at the state reached by
its predecessor. There are n edges and n+1 ghost operations. -/
def MarkedMemoryChronologicalHistory {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) : ℕ → MarkedRawState P (pads+1) B Z → Type _
  | 0,s => MarkedMemoryGhostChoice hZ s
  | n+1,s => Σ ghost : MarkedMemoryGhostChoice hZ s,
      Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
        MarkedMemoryChronologicalHistory hZ n
          (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge)

@[instance_reducible]
noncomputable def markedMemoryChronologicalHistory_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    (n : ℕ) → (s : MarkedRawState P (pads+1) B Z) → Fintype (MarkedMemoryChronologicalHistory hZ n s)
  | 0,s => markedMemoryGhostChoice_fintype hZ s
  | n+1,s => by
      letI : ∀ t : MarkedRawState P (pads+1) B Z, Fintype (MarkedMemoryChronologicalHistory hZ n t) :=
        markedMemoryChronologicalHistory_fintype (P := P) (pads := pads) (B := B) hZ n
      change Fintype (Σ ghost : MarkedMemoryGhostChoice hZ s,
        Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
          MarkedMemoryChronologicalHistory hZ n
            (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge))
      infer_instance

attribute [instance] markedMemoryChronologicalHistory_fintype

noncomputable def markedMemoryChronologicalTarget {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      MarkedMemoryChronologicalHistory hZ n s → MarkedRawState P (pads+1) B Z
  | 0,s,ghost => markedMemoryGhostChoiceTarget hZ s ghost
  | _+1,_,history => markedMemoryChronologicalTarget hZ history.2.2

noncomputable def markedMemoryChronologicalWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,s,ghost => markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s ghost
  | n+1,j,s,history =>
      markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s history.1*
        markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (χ j)
          (markedMemoryGhostChoiceTarget hZ s history.1) history.2.1*
        markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n (j+1) history.2.2

/-- The literal finite composition, before any boundary pairing or claim of
 lifespan correspondence. All cutoffs and signs are the original ones. -/
noncomputable def markedMemoryChronologicalApply {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    ℕ → ℕ → (MarkedRawState P (pads+1) B Z → ℂ) → MarkedRawState P (pads+1) B Z → ℂ
  | 0,j,f => markedRawGhostApply ν V (qStage j) ρ hZ f
  | n+1,j,f => markedRawGhostApply ν V (qStage j) ρ hZ
      (markedRawSlotAverage (markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ (χ j)
        (markedRawSlotAverage (markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n (j+1) f))))

/-- Genuine finite choice expansion of every chronological forward history.
No equality with the independent-line or lifespan expansion is assumed. -/
theorem markedMemoryChronological_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ history : MarkedMemoryChronologicalHistory hZ n s,
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history*
        f (markedMemoryChronologicalTarget hZ history)) =
      markedMemoryChronologicalApply ν V hZ ψ η d₀ Y Q ρ qStage χ n j f s := by
  classical
  induction n generalizing j s with
  | zero =>
    exact markedMemoryGhostChoice_sum ν V (qStage j) ρ hZ f s
  | succ n ih =>
    change (∑ history : Σ ghost : MarkedMemoryGhostChoice hZ s,
        Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
          MarkedMemoryChronologicalHistory hZ n
            (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge),
      (markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ (n+1) j history*
        f (markedMemoryChronologicalTarget hZ (n := n+1) (s := s) history) : ℂ)) = _
    simp only [Fintype.sum_sigma,markedMemoryChronologicalWeight,markedMemoryChronologicalTarget]
    simp_rw [mul_assoc,← Finset.mul_sum,ih]
    simp_rw [← Fintype.sum_sigma']
    simp_rw [markedMemoryEdgeChoice_sum]
    exact markedMemoryGhostChoice_sum ν V (qStage j) ρ hZ _ s

end ArtinMatthews
