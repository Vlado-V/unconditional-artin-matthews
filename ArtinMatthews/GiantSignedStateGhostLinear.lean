module

public import ArtinMatthews.GiantSignedStateGhostGroup


set_option backward.privateInPublic true
@[expose] public section

/-! Additivity of the literal countable ghost row follows from its
proved absolute convergence on each exponential input. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedStateGhost_summable
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (w : GiantSignedState PS PB M → ℂ) (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hw : ∀ s a m, ‖w (s, a, m)‖ ≤ Cf * u ^ (∑ g, m.1 g))
    (s : GiantSignedState PS PB M) :
    Summable (fun r : GiantSignedGhostMemoryMoves s.2.2 =>
      giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r *
        w (s.1, s.2.1, giantSignedGhostMemoryMoveTarget s.2.2 r)) :=
  (giantSignedGhostSimultaneous_summable_norm ν hν A C D
    (fun m => w (s.1, s.2.1, m)) Cf u hCf hu (hw s.1 s.2.1) s.2.2).of_norm

theorem giantSignedStateGhostApply_add
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostApply PS ν A C D (w₁+w₂) =
      giantSignedStateGhostApply PS ν A C D w₁ + giantSignedStateGhostApply PS ν A C D w₂ := by
  funext s
  have hs₁ := giantSignedStateGhost_summable PS ν hν A C D w₁ C₁ u₁ hC₁ hu₁ h₁ s
  have hs₂ := giantSignedStateGhost_summable PS ν hν A C D w₂ C₂ u₂ hC₂ hu₂ h₂ s
  simp only [giantSignedStateGhostApply, giantSignedGhostSimultaneousApply, Pi.add_apply, mul_add]
  exact hs₁.tsum_add hs₂

theorem giantSignedStateGhostApply_sub
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (w₁ w₂ : GiantSignedState PS PB M → ℂ)
    (C₁ u₁ C₂ u₂ : ℝ) (hC₁ : 0 ≤ C₁) (hu₁ : 0 < u₁) (hC₂ : 0 ≤ C₂) (hu₂ : 0 < u₂)
    (h₁ : ∀ s a m, ‖w₁ (s,a,m)‖ ≤ C₁ * u₁ ^ (∑ g, m.1 g))
    (h₂ : ∀ s a m, ‖w₂ (s,a,m)‖ ≤ C₂ * u₂ ^ (∑ g, m.1 g)) :
    giantSignedStateGhostApply PS ν A C D (w₁-w₂) =
      giantSignedStateGhostApply PS ν A C D w₁ - giantSignedStateGhostApply PS ν A C D w₂ := by
  funext s
  have hs₁ := giantSignedStateGhost_summable PS ν hν A C D w₁ C₁ u₁ hC₁ hu₁ h₁ s
  have hs₂ := giantSignedStateGhost_summable PS ν hν A C D w₂ C₂ u₂ hC₂ hu₂ h₂ s
  simp only [giantSignedStateGhostApply, giantSignedGhostSimultaneousApply, Pi.sub_apply, mul_sub]
  exact hs₁.tsum_sub hs₂

theorem giantSignedStateGhostApply_zero (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ) :
    giantSignedStateGhostApply PS ν A C D (0 : GiantSignedState PS PB M → ℂ) = 0 := by
  funext s
  simp only [giantSignedStateGhostApply, giantSignedGhostSimultaneousApply, Pi.zero_apply,
    mul_zero, tsum_zero]

end
end ArtinMatthews
