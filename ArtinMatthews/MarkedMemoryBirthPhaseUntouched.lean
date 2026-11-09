module

public import ArtinMatthews.MarkedMemoryBirthPhaseOperators
public import ArtinMatthews.MarkedMinorArcRawEdgeModifierSymmetrized
public import ArtinMatthews.MarkedMinorArcRawEdgeActualPartition


set_option backward.privateInPublic true
@[expose] public section

/-! An operation outside the moved-address image is exactly the original
operation, with its physical cutoffs and charges unchanged. In particular
the signed good-edge estimate remains available on every untouched edge. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

theorem markedMemoryGhostBirthPhaseApply_untouched
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (qStage ρ : ℝ) {M B n : ℕ}
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J M B n))
    (θ : MarkedMemoryPotentialAddress J M B n → AddCircle (1:ℝ)) (t : Fin (n+1))
    (ht : some (2*t.1) ∉ σ.support.image markedMemoryPotentialOperation)
    (f : MarkedRawState P M B Z → ℂ) :
    markedRawGhostBirthModifiedApply ν V qStage ρ hZ (markedMemoryGhostBirthPhase σ θ t) f =
      markedRawGhostApply ν V qStage ρ hZ f := by
  funext s
  unfold markedRawGhostBirthModifiedApply markedRawGhostModifiedApply
  simp_rw [markedMemoryGhostBirthPhase_eq_one σ θ t ht,one_mul]
  exact markedMemoryGhostChoice_sum ν V qStage ρ hZ f s

theorem markedMemoryEdgeBirthPhaseApply_untouched
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) {pads B n : ℕ}
    {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B n))
    (θ : MarkedMemoryPotentialAddress J (pads+1) B n → AddCircle (1:ℝ)) (t : Fin n)
    (ht : some (2*t.1+1) ∉ σ.support.image markedMemoryPotentialOperation)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ
      (markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhase σ θ t)) f =
        markedRawEdgeSymmetrized ν V hZ ψ η d₀ Y Q ρ χ f := by
  have hmod (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
      markedRawEdgeBirthModifier (markedMemoryEdgeBirthPhase σ θ t) s c = 1 := by
    apply Finset.prod_eq_one
    intro j _
    exact markedMemoryEdgeBirthPhase_eq_one σ θ t ht j _
  unfold markedRawEdgeModifiedSymmetrized markedRawEdgeSymmetrized
  congr 1
  funext s
  unfold markedRawEdgeModifiedApply markedRawEdgeApply
  apply Finset.sum_congr rfl
  intro c _
  rw [hmod,one_mul]

end ArtinMatthews
