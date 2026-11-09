module

public import ArtinMatthews.MarkedMemoryIndependentRunCount
public import ArtinMatthews.MarkedMemoryIndependentIncomingFiber
public import ArtinMatthews.MarkedMemoryIndependentBirthWeight


set_option backward.privateInPublic true
@[expose] public section

/-! The actual promotion fiber is exactly the direct finite set of edges
whose incoming identity is this lifespan and is already in old memory.
The resulting run-power identity retains the entire original residual. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order
local notation "addr" => markedMemoryIndependentAddressEquiv hZ d order

def markedMemoryIndependentRunFiberEquiv (a : Σ j, A j) :
    {r : MarkedMemoryHistoryPromotionIndex hZ history // markedMemoryHistoryPromotionOrigin hZ history r = (addr).symm a} ≃
      {v : Fin n // (d.lifespan a.1).incoming (2*v.val+1) = a.2 ∧
        a.2 ∈ markedMemoryIndependentQueue hZ d (2*v.val+1) a.1} := by
  let ep : {r : MarkedMemoryHistoryPromotionIndex hZ history //
      markedMemoryHistoryPromotionOrigin hZ history r = (addr).symm a} ≃
      {p : MarkedMemoryIndependentPromotions hZ d // markedMemoryIndependentPromotionLabel hZ d p = a} :=
    (markedMemoryIndependentPromotionEquiv hZ d order).subtypeEquiv (fun r => by
      have h := markedMemoryIndependentPromotion_origin hZ d order r
      constructor
      · intro hr
        exact h.symm.trans ((congrArg addr hr).trans ((addr).apply_symm_apply a))
      · intro hp
        apply (addr).injective
        exact h.trans (hp.trans ((addr).apply_symm_apply a).symm))
  let ef := markedMemoryIncomingLabelFiberEquiv
    (fun v : Fin n => fun j => (d.lifespan j).incoming (2*v.val+1))
    (fun v : Fin n => fun j => (d.lifespan j).incoming (2*v.val+1) ∈
      markedMemoryIndependentQueue hZ d (2*v.val+1) j) a
  refine ep.trans (ef.trans (Equiv.subtypeEquivRight (fun v => ?_)))
  constructor
  · rintro ⟨hi,hm⟩
    exact ⟨hi,by simpa only [hi] using hm⟩
  · rintro ⟨hi,hm⟩
    exact ⟨hi,by simpa only [hi] using hm⟩

theorem markedMemoryIndependent_runCount (a : Σ j, A j) :
    markedMemoryHistoryRunCount hZ history ((addr).symm a) = markedMemoryIndependentRunCount hZ d a := by
  unfold markedMemoryHistoryRunCount markedMemoryIndependentRunCount
  rw [Fintype.card_congr (markedMemoryIndependentRunFiberEquiv hZ d order a), Fintype.card_subtype]

theorem markedMemoryIndependent_runWeight
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) (offset : ℕ) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n offset history =
      ((∏ a : Σ j, A j, markedMemoryIndependentBirthMass hZ d ν V a *
        (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a : ℝ) : ℂ) *
      markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n offset history := by
  rw [markedMemoryChronologicalWeight_run_powers]
  congr 2
  rw [← Equiv.prod_comp (addr).symm]
  apply Finset.prod_congr rfl
  intro a _
  rw [markedMemoryIndependent_birthMass hZ d order ν V ((addr).symm a), (addr).apply_symm_apply,
    markedMemoryIndependent_runCount]
  have hg := markedMemoryIndependentAddress_group hZ d order ((addr).symm a)
  rw [(addr).apply_symm_apply] at hg
  rw [← hg]

end
end ArtinMatthews
