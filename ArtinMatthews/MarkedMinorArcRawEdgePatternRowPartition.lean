module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternFilteredRows


set_option backward.privateInPublic true
@[expose] public section

/-! Exact row splitting, before estimates: each choice either promotes
an indexed old prime or has no promoted group. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawEdgePatternWeightedRow_promotion_split
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A : MarkedRawEdgePatternKernel P pads B Z) (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ s =
      markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀ s +
        markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀ s := by
  unfold markedRawEdgePatternWeightedRow
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : markedRawEdgeChoicePromoted c = fun _ => false <;>
    simp [markedRawEdgePromotedKernel,markedRawEdgeNoPromotionKernel,markedRawEdgeFlagGate,hp]

theorem markedRawSlotAverageReal_add {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F G : MarkedRawState P M B Z → ℝ) :
    markedRawSlotAverageReal (F+G) = markedRawSlotAverageReal F + markedRawSlotAverageReal G := by
  funext s
  simp only [markedRawSlotAverageReal,Pi.add_apply,Finset.sum_add_distrib,mul_add]

theorem markedRawEdgePatternWeightedRow_average_promotion_split
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (δ γ : J → ℂ)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (A : MarkedRawEdgePatternKernel P pads B Z) (v₀ : ℝ) (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal (markedRawEdgePatternWeightedRow ν δ γ hZ A v₀) s =
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀) s +
      markedRawSlotAverageReal
        (markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀) s := by
  have h : markedRawEdgePatternWeightedRow ν δ γ hZ A v₀ =
      markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgePromotedKernel A) v₀ +
        markedRawEdgePatternWeightedRow ν δ γ hZ (markedRawEdgeNoPromotionKernel A) v₀ := by
    funext u
    exact markedRawEdgePatternWeightedRow_promotion_split ν δ γ hZ A v₀ u
  rw [h,markedRawSlotAverageReal_add]
  rfl

theorem markedRawEdgeStoreOnlyKernel_eq_noPromotion_stored
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeStoreOnlyKernel A = markedRawEdgeNoPromotionKernel (markedRawEdgeStoredKernel A) := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    simp [markedRawEdgeStoreOnlyKernel,markedRawEdgeNoPromotionKernel,
      markedRawEdgeStoredKernel,markedRawEdgeFlagGate,hp,hq]

theorem markedRawEdgeStoreOnlyKernel_reverse
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (A : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgePatternReverse (markedRawEdgeStoreOnlyKernel A) =
      markedRawEdgePromotedKernel
        (markedRawEdgeFlagGate (fun _ q => q = fun _ => false) (markedRawEdgePatternReverse A)) := by
  funext p q s t
  by_cases hp : p = fun _ => false <;> by_cases hq : q = fun _ => false <;>
    simp [markedRawEdgePatternReverse,markedRawEdgeStoreOnlyKernel,
      markedRawEdgePromotedKernel,markedRawEdgeFlagGate,hp,hq]

theorem markedRawEdgeFlagGate_mul
    {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (F : (J → Bool) → (J → Bool) → Prop) (A K : MarkedRawEdgePatternKernel P pads B Z) :
    markedRawEdgeFlagGate F (fun p q s t => A p q s t * K p q s t) =
      (fun p q s t => markedRawEdgeFlagGate F A p q s t * K p q s t) := by
  funext p q s t
  by_cases h : F p q <;> simp [markedRawEdgeFlagGate,h]

end
end ArtinMatthews
