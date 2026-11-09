module

public import ArtinMatthews.GiantSignedStateGhostLinear


set_option backward.privateInPublic true
@[expose] public section

/-! The source q/rho visit row has the same exact add/sub identities. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedStateGhostGroup_add
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostGroup PS ν V q ρ (w₁+w₂) =
      giantSignedStateGhostGroup PS ν V q ρ w₁ + giantSignedStateGhostGroup PS ν V q ρ w₂ :=
  giantSignedStateGhostApply_add PS ν hν _ _ _ w₁ w₂ C₁ u₁ C₂ u₂ hC₁ hu₁ hC₂ hu₂ h₁ h₂

theorem giantSignedStateGhostGroup_sub
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ : ℝ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostGroup PS ν V q ρ (w₁-w₂) =
      giantSignedStateGhostGroup PS ν V q ρ w₁ - giantSignedStateGhostGroup PS ν V q ρ w₂ :=
  giantSignedStateGhostApply_sub PS ν hν _ _ _ w₁ w₂ C₁ u₁ C₂ u₂ hC₁ hu₁ hC₂ hu₂ h₁ h₂

end
end ArtinMatthews
