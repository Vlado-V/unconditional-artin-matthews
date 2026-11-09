module

public import ArtinMatthews.MarkedMemoryPotentialBirths
public import Mathlib.Data.Prod.Lex


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine chronological linear order on actual potential birth
addresses: initial time zero, ghost time 2t+1, fresh-edge time 2t+2,
then a finite group rank and the literal within-group birth index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} {M B n : ℕ}

def markedMemoryPotentialChronologicalTime : MarkedMemoryPotentialAddress J M B n → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl ⟨t,_⟩) => 2*t.val+1
  | Sum.inr (Sum.inr ⟨t,_⟩) => 2*t.val+2

def markedMemoryPotentialGroup : MarkedMemoryPotentialAddress J M B n → J
  | Sum.inl ⟨j,_⟩ => j
  | Sum.inr (Sum.inl ⟨_,j,_⟩) => j
  | Sum.inr (Sum.inr ⟨_,j⟩) => j

def markedMemoryPotentialBatchIndex : MarkedMemoryPotentialAddress J M B n → ℕ
  | Sum.inl ⟨_,k⟩ => k.val
  | Sum.inr (Sum.inl ⟨_,_,k⟩) => k.val
  | Sum.inr (Sum.inr _) => 0

variable [Fintype J]

def markedMemoryPotentialChronologicalKey (a : MarkedMemoryPotentialAddress J M B n) :
    ℕ ×ₗ (Fin (Fintype.card J) ×ₗ ℕ) :=
  toLex (markedMemoryPotentialChronologicalTime a,
    toLex (Fintype.equivFin J (markedMemoryPotentialGroup a),markedMemoryPotentialBatchIndex a))

theorem markedMemoryPotentialChronologicalKey_injective :
    Function.Injective (markedMemoryPotentialChronologicalKey (J := J) (M := M) (B := B) (n := n)) := by
  intro a b he
  have ht := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card J) ×ₗ ℕ) => (ofLex u).1) he
  have hr := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card J) ×ₗ ℕ) => (ofLex (ofLex u).2).1) he
  have hk := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card J) ×ₗ ℕ) => (ofLex (ofLex u).2).2) he
  change markedMemoryPotentialChronologicalTime a=markedMemoryPotentialChronologicalTime b at ht
  change Fintype.equivFin J (markedMemoryPotentialGroup a)=Fintype.equivFin J (markedMemoryPotentialGroup b) at hr
  change markedMemoryPotentialBatchIndex a=markedMemoryPotentialBatchIndex b at hk
  have hj := (Fintype.equivFin J).injective hr
  rcases a with ⟨ja,ka⟩ | ⟨ta,ja,ka⟩ | ⟨ta,ja⟩ <;>
    rcases b with ⟨jb,kb⟩ | ⟨tb,jb,kb⟩ | ⟨tb,jb⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime,markedMemoryPotentialGroup,
      markedMemoryPotentialBatchIndex] at ht hj hk
  all_goals try omega
  · cases hj
    have hh : ka=kb := Fin.ext hk
    cases hh
    rfl
  · have hh : ta=tb := Fin.ext (by omega)
    cases hh
    cases hj
    have hh : ka=kb := Fin.ext hk
    cases hh
    rfl
  · have hh : ta=tb := Fin.ext (by omega)
    cases hh
    cases hj
    rfl

@[instance_reducible]
def markedMemoryPotentialChronologicalOrder :
    LinearOrder (MarkedMemoryPotentialAddress J M B n) :=
  LinearOrder.lift' markedMemoryPotentialChronologicalKey markedMemoryPotentialChronologicalKey_injective

def MarkedMemoryPotentialEarlier (a b : MarkedMemoryPotentialAddress J M B n) : Prop :=
  markedMemoryPotentialChronologicalKey a < markedMemoryPotentialChronologicalKey b

theorem markedMemoryPotentialEarlier_of_time {a b : MarkedMemoryPotentialAddress J M B n}
    (ht : markedMemoryPotentialChronologicalTime a < markedMemoryPotentialChronologicalTime b) :
    MarkedMemoryPotentialEarlier a b :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inl ht)

theorem markedMemoryPotentialEarlier_time {a b : MarkedMemoryPotentialAddress J M B n}
    (hab : MarkedMemoryPotentialEarlier a b) :
    markedMemoryPotentialChronologicalTime a ≤ markedMemoryPotentialChronologicalTime b :=
  Prod.Lex.monotone_fst _ _ (le_of_lt hab)

theorem markedMemoryPotentialEarlier_ghost_batch (t : Fin (n+1)) (j : J) {a b : Fin B}
    (hab : a<b) :
    MarkedMemoryPotentialEarlier (M := M) (Sum.inr (Sum.inl ⟨t,j,a⟩))
      (Sum.inr (Sum.inl ⟨t,j,b⟩)) :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,hab⟩)⟩)

theorem markedMemoryPotentialEarlier_initial_batch (j : J) {a b : Fin M}
    (hab : a<b) :
    MarkedMemoryPotentialEarlier (B := B) (n := n) (Sum.inl ⟨j,a⟩) (Sum.inl ⟨j,b⟩) :=
  Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,
    Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl,hab⟩)⟩)

end
end ArtinMatthews
