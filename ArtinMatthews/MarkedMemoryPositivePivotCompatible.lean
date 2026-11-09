module

public import ArtinMatthews.MarkedMemoryPositivePivotHistory
public import ArtinMatthews.MarkedMemoryPivotCompatible


set_option backward.privateInPublic true
@[expose] public section

/-! On a compatible history, the positive conditional weight is exactly
the norm of the original oriented history coefficient. This comparison
uses every gate and memo update; it is not a signed-to-absolute norm claim. -/

noncomputable section
namespace ArtinMatthews

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedMemoryPositivePivotHistoryWeight_of_compatible
    {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
    (ν : (i : J) → ↥(P i) → ℝ) (V : J → ℝ) {pads B N : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (orientation : ℕ → Bool) (qStage : ℕ → ℝ)
    (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (σ : Equiv.Perm (MarkedMemoryPotentialAddress J (pads+1) B N))
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z} (h : MarkedMemoryChronologicalHistory hZ n s)
    (old : MarkedMemoryPotentialAddress J (pads+1) B N → Option Nat.Primes)
    (hc : MarkedMemoryPivotCompatible hZ σ n j h old) :
    markedMemoryPositivePivotHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ σ n j h old =
      ‖markedMemoryGeometricHistoryWeight ν V hZ ψ η d₀ Y Q ρ orientation qStage χ n j h‖ := by
  induction n generalizing j s old with
  | zero =>
    obtain ⟨hg,hG⟩ := hc
    have hG' : markedMemoryGhostPivotGate σ ⟨j,hg⟩ old h.sizes.1 h.births :=
      (markedMemoryGhostPivotGate_iff σ ⟨j,hg⟩ old h.sizes.1 h.births).mpr hG
    rw [markedMemoryPositivePivotHistoryWeight,dite_eq_left hg,ite_eq_left hG']
    rfl
  | succ n ih =>
    obtain ⟨hg,hG,he,hE,hTail⟩ := hc
    have hG' : markedMemoryGhostPivotGate σ ⟨j,hg⟩ old h.1.sizes.1 h.1.births :=
      (markedMemoryGhostPivotGate_iff σ ⟨j,hg⟩ old h.1.sizes.1 h.1.births).mpr hG
    let afterGhost := markedMemoryGhostPivotValues ⟨j,hg⟩ old h.1.sizes.1 h.1.births
    let source := markedRawSlotEquiv h.2.1.1 (markedMemoryGhostChoiceTarget hZ s h.1)
    have hE' : markedMemoryEdgePivotGate σ ⟨j,he⟩ afterGhost hZ source h.2.1.2.1 :=
      (markedMemoryEdgePivotGate_iff σ ⟨j,he⟩ afterGhost hZ source h.2.1.2.1).mpr hE
    rw [markedMemoryPositivePivotHistoryWeight,dite_eq_left hg,ite_eq_left hG',dite_eq_left he]
    change (if markedMemoryEdgePivotGate σ ⟨j,he⟩ afterGhost hZ source h.2.1.2.1 then _ else 0)=_
    rw [ite_eq_left hE',ih (j+1) h.2.2 _ hTail]
    simp only [markedMemoryGeometricHistoryWeight,norm_mul]

end ArtinMatthews
