module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess
public import ArtinMatthews.MarkedMemoryHistoryRunPowers


set_option backward.privateInPublic true
@[expose] public section

/-! Enumerate genuine chronological promotions by their actual finite
edge vertex and promoted band. The map retains the original local
promotion occurrence; no numeric prime quotient is used. -/
namespace ArtinMatthews
noncomputable section

universe u

def markedMemorySigmaFinSuccEquiv {n : ℕ} (X : Fin (n+1) → Type u) :
    (X 0 ⊕ (Σ v : Fin n, X v.succ)) ≃ (Σ v : Fin (n+1), X v) where
  toFun := Sum.elim (fun x => ⟨0,x⟩) (fun x => ⟨x.1.succ,x.2⟩)
  invFun x := Fin.cases (fun a => Sum.inl a) (fun v a => Sum.inr ⟨v,a⟩) x.1 x.2
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨v,x⟩
    revert x
    refine Fin.cases ?_ (fun w => ?_) v
    · intro x; rfl
    · intro x; rfl

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistoryPromotionVertexEquiv :
    {n : ℕ} → {s : MarkedRawState P (pads+1) B Z} →
      (history : MarkedMemoryChronologicalHistory hZ n s) →
      MarkedMemoryHistoryPromotionIndex hZ history ≃
        (Σ v : Fin n, MarkedMemoryEdgePromotionIndex hZ (markedMemoryHistoryVertexEdge hZ history v))
  | 0,_,_ =>
      { toFun := PEmpty.elim
        invFun := fun x => Fin.elim0 x.1
        left_inv := fun x => PEmpty.elim x
        right_inv := fun x => Fin.elim0 x.1 }
  | _+1,_,history =>
      (Equiv.sumCongr (Equiv.refl _) (markedMemoryHistoryPromotionVertexEquiv history.2.2)).trans
        (markedMemorySigmaFinSuccEquiv (fun v =>
          MarkedMemoryEdgePromotionIndex hZ (markedMemoryHistoryVertexEdge hZ history v)))

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionVertex_group {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryPromotionGroup hZ history r =
      (markedMemoryHistoryPromotionVertexEquiv hZ history r).2.1 := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => rfl
    | inr r => exact ih history.2.2 r

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionVertex_time {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryPromotionTime hZ history r =
      2*(markedMemoryHistoryPromotionVertexEquiv hZ history r).1.val+1 := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => rfl
    | inr r =>
      have hi := ih history.2.2 r
      change markedMemoryHistoryPromotionTime hZ history.2.2 r+2 =
        2*((markedMemoryHistoryPromotionVertexEquiv hZ history.2.2 r).1.val+1)+1
      omega

omit [DecidableEq J] in
theorem markedMemoryHistoryPromotionVertex_target {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (r : MarkedMemoryHistoryPromotionIndex hZ history) :
    markedMemoryHistoryPromotionTarget hZ history r = Sum.inl
      ⟨(markedMemoryHistoryPromotionVertexEquiv hZ history r).2.1,
        ((markedMemoryHistoryVertexEdge hZ history (markedMemoryHistoryPromotionVertexEquiv hZ history r).1).2.2
          (markedMemoryHistoryPromotionVertexEquiv hZ history r).2.1).symm (Fin.last pads)⟩ := by
  induction n generalizing s with
  | zero => exact PEmpty.elim r
  | succ n ih =>
    cases r with
    | inl r => rfl
    | inr r => exact ih history.2.2 r

end
end ArtinMatthews
