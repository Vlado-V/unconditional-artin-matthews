module

public import ArtinMatthews.MarkedMinorArcRawEdgeAction
public import ArtinMatthews.MarkedMinorArcRawSlotAverage


set_option backward.privateInPublic true
@[expose] public section

/-! Literal indexed choices for a slot-symmetrized raw edge. Both endpoint
permutations, their probability weights, all old-only promotions and all
fresh-label choices are retained. -/
namespace ArtinMatthews
open scoped BigOperators

abbrev MarkedMemorySlotPermutations (J : Type*) (M : ℕ) := J → Equiv.Perm (Fin M)

abbrev MarkedMemoryEdgeChoice {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :=
  Σ sourceSlots : MarkedMemorySlotPermutations J (pads+1),
    MarkedRawEdgeChoice hZ (markedRawSlotEquiv sourceSlots s) ×
      MarkedMemorySlotPermutations J (pads+1)

noncomputable instance markedMemoryEdgeChoice_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Fintype (MarkedMemoryEdgeChoice hZ s) := by
  classical
  unfold MarkedMemoryEdgeChoice
  infer_instance

noncomputable def markedMemoryEdgeChoiceTarget {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedMemoryEdgeChoice hZ s) : MarkedRawState P (pads+1) B Z :=
  markedRawSlotEquiv choice.2.2
    (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1)

noncomputable def markedMemoryEdgeChoiceWeight {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s : MarkedRawState P (pads+1) B Z) (choice : MarkedMemoryEdgeChoice hZ s) : ℂ :=
  ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
    (markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv choice.1 s) choice.2.1:ℂ)*
    markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv choice.1 s) choice.2.1*
    ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)

/-- Exact finite expansion of the actual two slot averages and raw edge. -/
theorem markedMemoryEdgeChoice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (f : MarkedRawState P (pads+1) B Z → ℂ) (s : MarkedRawState P (pads+1) B Z) :
    (∑ choice : MarkedMemoryEdgeChoice hZ s,
      markedMemoryEdgeChoiceWeight ν V hZ ψ η d₀ Y Q ρ χ s choice*
        f (markedMemoryEdgeChoiceTarget hZ s choice)) =
      markedRawSlotAverage (markedRawEdgeApply ν V hZ ψ η d₀ Y Q ρ χ (markedRawSlotAverage f)) s := by
  classical
  unfold markedMemoryEdgeChoiceWeight markedMemoryEdgeChoiceTarget
  change (∑ choice : Σ σ : MarkedMemorySlotPermutations J (pads+1),
      MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) × MarkedMemorySlotPermutations J (pads+1),
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
        (markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv choice.1 s) choice.2.1:ℂ)*
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv choice.1 s) choice.2.1*
        ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)):ℂ)⁻¹)*
        f (markedRawSlotEquiv choice.2.2 (markedRawEdgeTargetState hZ (markedRawSlotEquiv choice.1 s) choice.2.1))) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  unfold markedRawSlotAverage markedRawEdgeApply
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro edge _
  apply Finset.sum_congr rfl
  intro τ _
  ring

end ArtinMatthews
