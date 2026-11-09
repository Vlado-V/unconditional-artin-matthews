module

public import ArtinMatthews.MarkedMemoryPotentialChronology


set_option backward.privateInPublic true
@[expose] public section

/-! The chronological comparison splits into an earlier actual
operation, an earlier finite group in the same operation, or an earlier
literal batch index in the same group and operation. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {M B n : ℕ}

theorem markedMemoryPotentialEarlier_iff (a b : MarkedMemoryPotentialAddress J M B n) :
    MarkedMemoryPotentialEarlier a b ↔
      markedMemoryPotentialChronologicalTime a < markedMemoryPotentialChronologicalTime b ∨
      markedMemoryPotentialChronologicalTime a=markedMemoryPotentialChronologicalTime b ∧
        (Fintype.equivFin J (markedMemoryPotentialGroup a) < Fintype.equivFin J (markedMemoryPotentialGroup b) ∨
          markedMemoryPotentialGroup a=markedMemoryPotentialGroup b ∧
            markedMemoryPotentialBatchIndex a < markedMemoryPotentialBatchIndex b) := by
  unfold MarkedMemoryPotentialEarlier markedMemoryPotentialChronologicalKey
  rw [Prod.Lex.toLex_lt_toLex,Prod.Lex.toLex_lt_toLex,(Fintype.equivFin J).injective.eq_iff]

omit [Fintype J] in
theorem markedMemoryPotentialChronologicalTime_operation (a : MarkedMemoryPotentialAddress J M B n) :
    markedMemoryPotentialChronologicalTime a=
      match markedMemoryPotentialOperation a with
      | none => 0
      | some t => t+1 := by
  rcases a with ⟨j,k⟩ | ⟨t,j,k⟩ | ⟨t,j⟩ <;>
    simp only [markedMemoryPotentialChronologicalTime,markedMemoryPotentialOperation,Nat.add_assoc]

end
end ArtinMatthews
