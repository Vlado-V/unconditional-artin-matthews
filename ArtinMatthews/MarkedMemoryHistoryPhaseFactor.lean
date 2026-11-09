module

public import ArtinMatthews.MarkedMemoryBirthPhaseHistory
public import ArtinMatthews.MarkedMemoryHistoryLocalBirthProduct
public import ArtinMatthews.MarkedMemoryBirthPhaseBoundary


set_option backward.privateInPublic true
@[expose] public section

/-! The local operator phases factor the original oriented history
coefficient exactly. Initial phases and every actual performed birth stay
separate from the geometric coefficient and the literal boundary. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryGhostBirthValueFactorAt {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (i : J) (k : Fin B) (p : Option Nat.Primes) : ℂ :=
  if hj : j < N+1 then markedBirthLocalMultiplier σ θ (Sum.inr (Sum.inl (⟨j,hj⟩,(i,k)))) p else 1

theorem markedMemoryGhostLocalBirthProduct_at {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B N : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    {s : MarkedRawState P M B Z} (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostLocalBirthProduct (markedMemoryGhostBirthValueFactorAt σ θ) j c =
      markedMemoryGhostBirthPhaseAt σ θ j c.sizes.1 c.births := by
  by_cases hj : j < N+1
  · simp only [markedMemoryGhostLocalBirthProduct,markedMemoryGhostBirthValueFactorAt,
      markedMemoryGhostBirthPhaseAt,dite_eq_left hj]
    rfl
  · simp only [markedMemoryGhostLocalBirthProduct,markedMemoryGhostBirthValueFactorAt,
      markedMemoryGhostBirthPhaseAt,dite_eq_right hj,Finset.prod_const_one]

theorem markedMemoryEdgeLocalBirthProduct_at {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z, IsCoprime z.1 z.2}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (j : ℕ)
    {s : MarkedRawState P (pads+1) B Z} (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeLocalBirthProduct (markedMemoryEdgeBirthPhaseAt σ θ) j c =
      markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j) (markedRawSlotEquiv c.1 s) c.2.1 := rfl

theorem markedMemoryBirthLocalProduct_eq_initial_history
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    {pads B N : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ N s)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) :
    markedMemoryBirthLocalProduct hZ h σ θ = markedMemoryBirthInitialPhase σ θ s *
      markedMemoryHistoryLocalBirthProduct hZ (markedMemoryGhostBirthValueFactorAt σ θ)
        (markedMemoryEdgeBirthPhaseAt σ θ) N 0 h := by
  rw [markedMemoryBirthLocalProduct_split,markedMemoryHistoryLocalBirthProduct_eq_visits]
  simp only [Nat.zero_add,markedMemoryGhostBirthValueFactorAt,markedMemoryEdgeBirthPhaseAt,
    markedMemoryEdgeBirthPhase,Fin.isLt,dite_true]
  unfold markedMemoryBirthInitialPhase
  ring

def markedMemoryGeometricEdgeChoiceWeight
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (j : ℕ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  if orientation j then markedMemoryEdgeChoiceWeight ν V hZ (markedRawEdgeAdjointCutoff ψ)
    (fun u => star (η u)) d₀ Y Q ρ (fun u => star (χ j u)) s c
  else markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ (χ j) s c

def markedMemoryGeometricHistoryWeight
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    (n j : ℕ) → {s : MarkedRawState P (pads+1) B Z} → MarkedMemoryChronologicalHistory hZ n s → ℂ
  | 0,j,s,h => markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h
  | n+1,j,s,h => markedMemoryGhostChoiceWeight ν V (qStage j) ρ hZ s h.1 *
      markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation χ j
        (markedMemoryGhostChoiceTarget hZ s h.1) h.2.1 *
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n (j+1) h.2.2

theorem markedMemoryBirthPhaseEdgeWeight_factor
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (j : ℕ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryBirthPhaseEdgeWeight ν V hZ ψ η d₀ Y Q ρ orientation χ σ θ j s c =
      markedMemoryGeometricEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ orientation χ j s c *
        markedMemoryEdgeLocalBirthProduct (markedMemoryEdgeBirthPhaseAt σ θ) j c := by
  rw [markedMemoryEdgeLocalBirthProduct_at]
  unfold markedMemoryBirthPhaseEdgeWeight markedMemoryGeometricEdgeChoiceWeight
  split <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryBirthPhaseHistoryWeight_factor
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ))
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryBirthPhaseHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ n j h =
      markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n j h *
        markedMemoryHistoryLocalBirthProduct hZ (markedMemoryGhostBirthValueFactorAt σ θ)
          (markedMemoryEdgeBirthPhaseAt σ θ) n j h := by
  induction n generalizing j s with
  | zero =>
    rw [markedMemoryBirthPhaseHistoryWeight,markedMemoryGeometricHistoryWeight,
      markedMemoryHistoryLocalBirthProduct,markedMemoryGhostLocalBirthProduct_at]
  | succ n ih =>
    rw [markedMemoryBirthPhaseHistoryWeight,markedMemoryGeometricHistoryWeight,
      markedMemoryHistoryLocalBirthProduct,markedMemoryBirthPhaseEdgeWeight_factor,
      markedMemoryGhostLocalBirthProduct_at,ih]
    ring

end ArtinMatthews
