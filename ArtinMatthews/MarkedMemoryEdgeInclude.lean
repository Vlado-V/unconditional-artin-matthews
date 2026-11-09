module

public import ArtinMatthews.MarkedRawEdgeInclude


set_option backward.privateInPublic true
@[expose] public section

/-! Both actual slot permutations commute with restriction of the
position space. No permutation or probability factor is discarded. -/

noncomputable section
namespace ArtinMatthews

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z W : Finset (ℤ × ℤ)} (h : Z ⊆ W)
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (hW : ∀ z∈W,IsCoprime z.1 z.2)

def markedMemoryEdgeChoiceInclude (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) :
    MarkedMemoryEdgeChoice hW (markedRawStateInclude h s) :=
  ⟨c.1,markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1,c.2.2⟩

def markedMemoryEdgeChoiceWindowEquiv (s : MarkedRawState P (pads+1) B Z) :
    MarkedMemoryEdgeChoice hZ s ≃
      {c : MarkedMemoryEdgeChoice hW (markedRawStateInclude h s) // c.2.1.target.1∈Z} where
  toFun c := ⟨markedMemoryEdgeChoiceInclude h hZ hW s c,c.2.1.target.2⟩
  invFun c := ⟨c.1.1,
    (markedRawEdgeChoiceWindowEquiv h hZ hW (markedRawSlotEquiv c.1.1 s)).symm ⟨c.1.2.1,c.2⟩,
    c.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem markedMemoryEdgeChoiceInclude_target (s : MarkedRawState P (pads+1) B Z)
    (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceTarget hW (markedRawStateInclude h s)
      (markedMemoryEdgeChoiceInclude h hZ hW s c)=
      markedRawStateInclude h (markedMemoryEdgeChoiceTarget hZ s c) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryEdgeChoiceInclude_weight [DecidableEq J]
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B W → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) :
    markedMemoryEdgeChoiceWeight ν V hW ψ η d₀ Y Q ρ χ (markedRawStateInclude h s)
      (markedMemoryEdgeChoiceInclude h hZ hW s c)=
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ
        (fun s => χ (markedRawStateInclude h s)) s c := by
  change ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      (markedRawEdgeChoicePrimeMass ν V hW
        (markedRawStateInclude h (markedRawSlotEquiv c.1 s))
        (markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1):ℂ)*
      markedRawEdgeChoiceCoefficient hW ψ η d₀ Y Q ρ χ
        (markedRawStateInclude h (markedRawSlotEquiv c.1 s))
        (markedRawEdgeChoiceInclude h hZ hW (markedRawSlotEquiv c.1 s) c.2.1)*
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)=_
  rw [markedRawEdgeChoiceInclude_mass,markedRawEdgeChoiceInclude_coefficient]
  rfl

end ArtinMatthews
