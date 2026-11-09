module

public import ArtinMatthews.MarkedMemoryBirthPhaseUntouched
public import ArtinMatthews.MarkedMemoryGeometricWordEnergy
public import ArtinMatthews.MarkedWeightedMixedOperatorWord


set_option backward.privateInPublic true
@[expose] public section

/-! A literal chronological word with local performed-birth phases and
either physical geometric orientation at each edge. Original ν, V^-1
promotion charges, ghost factorials and both slot averages are retained. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedMemoryGhostBirthPhaseAt {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (l : J → Fin (B+1)) (births : (i : J) → Fin (l i:ℕ) → ↥(P i)) : ℂ :=
  if hj : j < N+1 then markedMemoryGhostBirthPhase σ θ ⟨j,hj⟩ l births else 1

def markedMemoryEdgeBirthPhaseAt {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (i : J) (p : Option Nat.Primes) : ℂ :=
  if hj : j < N then markedMemoryEdgeBirthPhase σ θ ⟨j,hj⟩ i p else 1

def MarkedMemoryBirthEdgeModified {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N)) (j : ℕ) : Prop :=
  j < N ∧ some (2*j+1) ∈ σ.support.image markedMemoryPotentialOperation

theorem markedMemoryGhostBirthPhaseAt_norm_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (l : J → Fin (B+1)) (births : (i : J) → Fin (l i:ℕ) → ↥(P i)) :
    ‖markedMemoryGhostBirthPhaseAt σ θ j l births‖ ≤ 1 := by
  unfold markedMemoryGhostBirthPhaseAt
  split_ifs
  · exact markedMemoryGhostBirthPhase_norm_le σ θ _ l births
  · simp

theorem markedMemoryEdgeBirthPhaseAt_norm_le {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (i : J) (p : Option Nat.Primes) : ‖markedMemoryEdgeBirthPhaseAt σ θ j i p‖ ≤ 1 := by
  unfold markedMemoryEdgeBirthPhaseAt
  split_ifs
  · exact markedMemoryEdgeBirthPhase_norm_le σ θ _ i p
  · simp

theorem markedMemoryEdgeBirthPhaseAt_unmodified {J : Type*} [Fintype J] [DecidableEq J] {M B N : ℕ}
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B N))
    (θ : MarkedMemoryPotentialAddress J M B N → AddCircle (1:ℝ)) (j : ℕ)
    (hj : ¬MarkedMemoryBirthEdgeModified σ j) (i : J) (p : Option Nat.Primes) :
    markedMemoryEdgeBirthPhaseAt σ θ j i p = 1 := by
  unfold markedMemoryEdgeBirthPhaseAt
  split_ifs with h
  · exact markedMemoryEdgeBirthPhase_eq_one σ θ ⟨j,h⟩ (fun hm => hj ⟨h,hm⟩) i p
  · rfl

theorem markedMemoryEdgeBirthPhaseAtApply_unmodified
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) (j : ℕ)
    (hj : ¬MarkedMemoryBirthEdgeModified σ j) (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ
      (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j)) f =
        markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f := by
  have hm (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
      markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j) s c = 1 :=
    Finset.prod_eq_one (fun i _ => markedMemoryEdgeBirthPhaseAt_unmodified σ θ j hj i _)
  unfold markedRawEdgeModifiedSymmetrized markedRawEdgeSymmetrized
  congr 1
  funext s
  unfold markedRawEdgeModifiedApply markedRawEdgeApply
  apply Finset.sum_congr rfl
  intro c _
  rw [hm,one_mul]

def markedMemoryBirthPhaseWord
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ)) :=
  markedOperatorWord
    (fun j => markedRawGhostBirthModifiedApply ν V (qStage j) ρ hZ (markedMemoryGhostBirthPhaseAt σ θ j))
    (fun j => if orientation j then
      markedRawEdgeModifiedSymmetrized ν V hZ (markedRawEdgeAdjointCutoff ψ) (fun u => star (η u))
        d₀ Y Q ρ (fun s => star (χ j s))
        (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j))
      else markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ (χ j)
        (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhaseAt σ θ j)))

theorem markedMemoryBirthPhaseWord_symmetric
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (hχ : ∀ j z a, MarkedRawMemorySymmetric (fun m => χ j (z,(a,m))))
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B N → AddCircle (1:ℝ))
    (f : MarkedRawState P (pads+1) B Z → ℂ)
    (hf : ∀ z a, MarkedRawMemorySymmetric (fun m => f (z,(a,m)))) (n j : ℕ) :
    ∀ z a, MarkedRawMemorySymmetric (fun m =>
      markedMemoryBirthPhaseWord ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ θ n j f (z,(a,m))) := by
  apply markedOperatorWord_mem (fun F => ∀ z a, MarkedRawMemorySymmetric (fun m => F (z,(a,m))))
  · intro i F hF
    exact markedRawGhostBirthModifiedApply_symmetric ν V (qStage i) ρ hZ _ F hF
  · intro i F hF
    by_cases hi : orientation i
    · simp only [ite_eq_left hi]
      exact markedRawEdgeBirthModifiedSymmetrized_symmetric ν V hZ _ _ _ _ _ _ _ F _
        (fun z a m τ => congrArg star (hχ i z a m τ)) hF
    · simp only [ite_eq_right hi]
      exact markedRawEdgeBirthModifiedSymmetrized_symmetric ν V hZ _ _ _ _ _ _ _ F _ (hχ i) hF
  · exact hf

end ArtinMatthews
