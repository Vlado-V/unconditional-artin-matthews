module

public import ArtinMatthews.MarkedMemoryBirthPhaseWord


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite choice expansion of both slot averages with a fresh-birth
modifier. The modifier is evaluated at the canonical target before the
literal final slot permutation. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedMemoryEdgeBirthModifiedWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (φ : J → Option Nat.Primes → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (c : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s c *
    markedRawEdgeBirthModifier φ (markedRawSlotEquiv c.1 s) c.2.1

theorem markedMemoryEdgeBirthModifiedChoice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (φ : J → Option Nat.Primes → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ c : MarkedMemoryEdgeChoice hZ s, markedMemoryEdgeBirthModifiedWeight ν V hZ ψ η d₀ Y Q ρ χ φ s c *
      f (markedMemoryEdgeChoiceTarget hZ s c)) =
      markedRawEdgeModifiedSymmetrized ν V hZ ψ η d₀ Y Q ρ χ (markedRawEdgeBirthModifier φ) f s := by
  classical
  unfold markedMemoryEdgeBirthModifiedWeight markedMemoryEdgeChoiceWeight markedMemoryEdgeChoiceTarget
  change (∑ c : Σ σ : MarkedMemorySlotPermutations J (pads+1),
      MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) × MarkedMemorySlotPermutations J (pads+1),
    ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      (markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv c.1 s) c.2.1:ℂ)*
      markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv c.1 s) c.2.1*
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
      markedRawEdgeBirthModifier φ (markedRawSlotEquiv c.1 s) c.2.1 *
      f (markedRawSlotEquiv c.2.2 (markedRawEdgeTargetState hZ (markedRawSlotEquiv c.1 s) c.2.1))) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  unfold markedRawEdgeModifiedSymmetrized markedRawSlotAverage markedRawEdgeModifiedApply
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro τ _
  ring

end ArtinMatthews
