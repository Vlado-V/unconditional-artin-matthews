module

public import ArtinMatthews.MarkedRawStateInclude
public import ArtinMatthews.MarkedMemoryHistoryGhostChoice


set_option backward.privateInPublic true
@[expose] public section

/-! A position-window inclusion changes none of the actual ghost choices,
anchors, factorials or signed coefficients. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {M B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedMemoryGhostChoiceInclude (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    MarkedMemoryGhostChoice hW (markedRawStateInclude h s) where
  deletion := c.deletion
  allowed := c.allowed
  sizes := c.sizes
  births := c.births

def markedMemoryGhostChoiceIncludeEquiv (s : MarkedRawState P M B Z) :
    MarkedMemoryGhostChoice hZ s ≃ MarkedMemoryGhostChoice hW (markedRawStateInclude h s) where
  toFun := markedMemoryGhostChoiceInclude h hZ hW s
  invFun c := ⟨c.deletion,c.allowed,c.sizes,c.births⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedMemoryGhostChoiceInclude_target (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceTarget hW (markedRawStateInclude h s)
      (markedMemoryGhostChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedMemoryGhostChoiceTarget hZ s c) := rfl

theorem markedMemoryGhostChoiceInclude_weight (ν : (j : J) → ↥(P j) → ℝ)
    (V : J → ℝ) (q ρ : ℝ) (s : MarkedRawState P M B Z)
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceWeight ν V q ρ hW (markedRawStateInclude h s)
      (markedMemoryGhostChoiceInclude h hZ hW s c)=
      markedMemoryGhostChoiceWeight ν V q ρ hZ s c := rfl

end ArtinMatthews
