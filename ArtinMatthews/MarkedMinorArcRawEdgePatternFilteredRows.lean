module

public import ArtinMatthews.MarkedMinorArcRawEdgePatternPartition
public import ArtinMatthews.MarkedMinorArcRawEdgePatternMinorRows
public import ArtinMatthews.MarkedMinorArcDirtyPromotedRow
public import ArtinMatthews.MarkedMinorArcRawEdgeNoPromotionActual


set_option backward.privateInPublic true
@[expose] public section

/-! Exact filtered rows joining the flag transpose to the arithmetic
promoted and no-promotion estimates. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeNoPromotionKernel {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (A : MarkedRawEdgePatternKernel P pads B Z) : MarkedRawEdgePatternKernel P pads B Z :=
  markedRawEdgeFlagGate (fun p _ => p = fun _ => false) A

theorem markedRawEdgeChoice_promoted_empty_iff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z,IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedRawEdgeChoice hZ s) :
    markedDirtyEdgePromotedGroups c.promotions = ∅ ↔ markedRawEdgeChoicePromoted c = fun _ => false := by
  constructor
  · intro h
    funext j
    have hn : c.promotions j = none := by
      by_contra hne
      have hj : j ∈ markedDirtyEdgePromotedGroups c.promotions := by
        simp [markedDirtyEdgePromotedGroups,hne]
      exact Finset.notMem_empty j (h ▸ hj)
    simp only [markedRawEdgeChoicePromoted,hn,Option.isSome_none]
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro j hj
    have hn : c.promotions j ≠ none := by simpa [markedDirtyEdgePromotedGroups] using hj
    have hf := congrFun h j
    change (c.promotions j).isSome = false at hf
    cases hp : c.promotions j with
    | none => exact hn hp
    | some k => simp [hp] at hf

theorem markedRawEdgeChoice_promoted_nonempty_iff {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    {hZ : ∀ z ∈ Z,IsCoprime z.1 z.2} {s : MarkedRawState P (pads+1) B Z}
    (c : MarkedRawEdgeChoice hZ s) :
    (markedDirtyEdgePromotedGroups c.promotions).Nonempty ↔
      markedRawEdgeChoicePromoted c ≠ fun _ => false := by
  rw [Finset.nonempty_iff_ne_empty]
  exact not_congr (markedRawEdgeChoice_promoted_empty_iff c)

theorem markedRawEdgePattern_promoted_average_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (r d₀ Y Q ρ v₀ : ℝ) (w : Z → ℤ × ℤ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (β : MarkedRawEdgePatternKernel P pads B Z)
    (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgePromotedKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (markedRawFirstGoodCutoff r d₀ Y w χ) u v)) v₀) s =
      markedDirtyPromotedWeightedRow ν V hZ ψ η r d₀ Y Q ρ v₀ w χ s
        (fun σ c => β (markedRawEdgeChoicePromoted c) c.store (markedRawSlotEquiv σ s)
          (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ s) c)) := by
  have hA : markedRawEdgePromotedKernel (fun p q u v => β p q u v *
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (markedRawFirstGoodCutoff r d₀ Y w χ) u v) =
      (fun p q u v => (if p ≠ (fun _ => false) then β p q u v else 0) *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ (markedRawFirstGoodCutoff r d₀ Y w χ) u v) := by
    funext p q u v
    by_cases hp : p = fun _ => false <;> simp [markedRawEdgePromotedKernel,markedRawEdgeFlagGate,hp]
  rw [hA,markedRawEdgePatternWeightedRow_minor_average ν V hν hV]
  unfold markedDirtyPromotedWeightedRow
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  by_cases hi : (markedDirtyEdgePromotedGroups c.promotions).Nonempty
  · have hp := (markedRawEdgeChoice_promoted_nonempty_iff c).mp hi
    simp [hi,hp]
  · have hp : markedRawEdgeChoicePromoted c = (fun _ => false) := by
      by_contra hn
      exact hi ((markedRawEdgeChoice_promoted_nonempty_iff c).mpr hn)
    simp [hi,hp]

theorem markedRawEdge_noPromotion_choice_sum {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (F : MarkedRawEdgeChoice hZ s → ℝ) :
    (∑ c : MarkedRawEdgeChoice hZ s,if markedRawEdgeChoicePromoted c = (fun _ => false) then F c else 0) =
      ∑ c : MarkedDirtyFixedEdgeChoice hZ s ∅,F c.1 := by
  simp_rw [← markedRawEdgeChoice_promoted_empty_iff]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun c : MarkedRawEdgeChoice hZ s =>
    markedDirtyEdgePromotedGroups c.promotions = ∅)) (by simp) F

theorem markedRawEdgePattern_noPromotion_average_eq
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (hν : ∀ j p,0 ≤ ν j p) (hV : ∀ j,0 < V j)
    {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ v₀ : ℝ)
    (χ : MarkedRawState P (pads+1) B Z → ℂ) (β : MarkedRawEdgePatternKernel P pads B Z)
    (s : MarkedRawState P (pads+1) B Z) :
    markedRawSlotAverageReal
      (markedRawEdgePatternWeightedRow ν (fun j => ((V j)⁻¹ : ℝ)) (fun _ => 1) hZ
        (markedRawEdgeNoPromotionKernel (fun p q u v => β p q u v *
          markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v)) v₀) s =
      markedRawEdgeNoPromotionSymWeightedRow ν V hZ ψ η d₀ Y Q ρ v₀ χ s
        (fun σ c => β (markedRawEdgeChoicePromoted c) c.store (markedRawSlotEquiv σ s)
          (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ s) c)) := by
  have hA : markedRawEdgeNoPromotionKernel (fun p q u v => β p q u v *
      markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) =
      (fun p q u v => (if p = (fun _ => false) then β p q u v else 0) *
        markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ u v) := by
    funext p q u v
    by_cases hp : p = fun _ => false <;> simp [markedRawEdgeNoPromotionKernel,markedRawEdgeFlagGate,hp]
  rw [hA,markedRawEdgePatternWeightedRow_minor_average ν V hν hV]
  unfold markedRawEdgeNoPromotionSymWeightedRow markedRawEdgeNoPromotionWeightedRow
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  let F := fun c : MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) =>
    markedRawEdgeChoicePrimeMass ν V hZ (markedRawSlotEquiv σ s) c *
      ‖β (markedRawEdgeChoicePromoted c) c.store (markedRawSlotEquiv σ s)
        (markedRawEdgeTargetState hZ (markedRawSlotEquiv σ s) c) *
        markedRawEdgeChoiceCoefficient hZ ψ η d₀ Y Q ρ χ (markedRawSlotEquiv σ s) c‖ *
      (markedRawMemorySchurWeight v₀ (markedRawEdgeTargetMemory hZ (markedRawSlotEquiv σ s) c) /
        markedRawMemorySchurWeight v₀ (markedRawSlotEquiv σ s).2.2)
  refine Eq.trans ?_ (markedRawEdge_noPromotion_choice_sum hZ (markedRawSlotEquiv σ s) F)
  apply Finset.sum_congr rfl
  intro c _
  by_cases hp : markedRawEdgeChoicePromoted c = fun _ => false <;> simp [hp,F]

end
end ArtinMatthews
