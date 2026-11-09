module

public import ArtinMatthews.MarkedMemoryHistoryGhostOrigins
public import ArtinMatthews.MarkedMemoryChoiceExt


set_option backward.privateInPublic true
@[expose] public section

/-! The deletion mask and the exact target state determine every literal
ghost coordinate, including the birth sizes and ordered birth primes. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryGhostTransport {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedMemoryGhostChoice hZ s) : MarkedMemoryGhostChoice hZ t :=
  cast (congrArg (MarkedMemoryGhostChoice hZ) h) c

theorem markedMemoryGhostTransport_heq {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedMemoryGhostChoice hZ s) : HEq c (markedMemoryGhostTransport hZ h c) := by
  cases h
  rfl

theorem markedMemoryGhostTransport_target {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedMemoryGhostChoice hZ s) :
    markedMemoryGhostChoiceTarget hZ t (markedMemoryGhostTransport hZ h c) = markedMemoryGhostChoiceTarget hZ s c := by
  cases h
  rfl

theorem markedMemoryGhostTransport_deletion_mem {s t : MarkedRawState P (pads+1) B Z} (h : s = t)
    (c : MarkedMemoryGhostChoice hZ s) (j : J) (k : Fin (t.2.2.1.1 j : ℕ)) :
    k ∈ (markedMemoryGhostTransport hZ h c).deletion j ↔
      Fin.cast (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ)) h.symm) k ∈ c.deletion j := by
  cases h
  rfl

theorem markedMemoryGhostChoice_eq_of_deletion_target {s : MarkedRawState P (pads+1) B Z}
    (a b : MarkedMemoryGhostChoice hZ s) (hd : a.deletion = b.deletion)
    (ht : markedMemoryGhostChoiceTarget hZ s a = markedMemoryGhostChoiceTarget hZ s b) : a = b := by
  rcases a with ⟨da,ha,la,ba⟩
  rcases b with ⟨db,hb,lb,bb⟩
  dsimp only at hd
  cases hd
  have hl : la = lb := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    have he := congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ)) ht
    change (markedRawGhostSurvivors s.2.2 da j).card + (la.1 j : ℕ) =
      (markedRawGhostSurvivors s.2.2 da j).card + (lb.1 j : ℕ) at he
    omega
  cases hl
  have hbirth : ba = bb := by
    funext j k
    have hm := congrArg (fun q : MarkedRawState P (pads+1) B Z => q.2.2) ht
    have hvalues := eq_of_heq (Sigma.mk.inj hm).2
    have he := congrFun (congrFun hvalues j)
      ((markedMemoryGhostOrigin s.2.2 da la j).symm (Sum.inr k))
    change (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) da la ba).2 j _ =
      (markedRawGhostTargetMemory s.2.2 s.1.1 (hZ _ s.1.2) da la bb).2 j _ at he
    rw [markedMemoryGhostOrigin_birth,markedMemoryGhostOrigin_birth] at he
    exact congrArg Sigma.fst he
  cases hbirth
  rfl

end
end ArtinMatthews
