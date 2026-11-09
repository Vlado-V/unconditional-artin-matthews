module

public import ArtinMatthews.MarkedRawStateInclude
public import ArtinMatthews.MarkedMemoryHistoryEdgeChoice
public import ArtinMatthews.MarkedMinorArcRawEdgeSymmetryCoefficients


set_option backward.privateInPublic true
@[expose] public section

/-! The actual raw edge embeds into a larger finite position space.
Its image consists exactly of choices whose target is in the smaller
window; all old indices, stores, fresh draws and both caps are literal. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedRawEdgeChoiceInclude (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    MarkedRawEdgeChoice hW (markedRawStateInclude h s) where
  target := ⟨c.target.1,h c.target.2⟩
  store := c.store
  promotions := c.promotions
  fresh := c.fresh
  promotion_hits := c.promotion_hits
  memory_bound := c.memory_bound

def markedRawEdgeChoiceWindowEquiv (s : MarkedRawState P (pads+1) B Z) :
    MarkedRawEdgeChoice hZ s ≃
      {c : MarkedRawEdgeChoice hW (markedRawStateInclude h s) // c.target.1∈Z} where
  toFun c := ⟨markedRawEdgeChoiceInclude h hZ hW s c,c.target.2⟩
  invFun c := ⟨⟨c.1.target.1,c.2⟩,c.1.store,c.1.promotions,c.1.fresh,
    c.1.promotion_hits,c.1.memory_bound⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedRawEdgeChoiceInclude_target (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeTargetState hW (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedRawEdgeTargetState hZ s c) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedRawEdgeChoiceInclude_mass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoicePrimeMass ν V hW (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=markedRawEdgeChoicePrimeMass ν V hZ s c := by
  simp only [markedRawEdgeChoicePrimeMass_eq_targetLast]
  rfl

theorem markedRawEdgeChoiceInclude_coefficient [DecidableEq J]
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B W → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedRawEdgeChoice hZ s) :
    markedRawEdgeChoiceCoefficient hW ψ η d₀ Y Q ρ χ (markedRawStateInclude h s)
      (markedRawEdgeChoiceInclude h hZ hW s c)=
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ (fun s => χ (markedRawStateInclude h s)) s c := rfl

end ArtinMatthews
