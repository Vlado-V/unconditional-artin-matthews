module

public import ArtinMatthews.MarkedMemoryPrimeLifespanTerminal


set_option backward.privateInPublic true
@[expose] public section

/-! The optional ghost endpoints are recovered from the parity of the
actual half-step birth/death interval. This is an identity for every
compatible used lifespan, rather than an assumed endpoint coding. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ}

def markedMemoryPrimeChoiceOfInterval (first last : Fin (2*N+2)) : MarkedMemoryPrimeLifespanChoice N :=
  ((if first.val%2=1 then some ⟨first.val/2,by have hh:=first.isLt; omega⟩ else none),
    (if last.val%2=0 then some ⟨last.val/2,by have hh:=last.isLt; omega⟩ else none))

variable {L : Type*} (line : Fin (N+1) → L)
  (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N)

theorem markedMemoryPrimeChoice_recover
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c) :
    markedMemoryPrimeChoiceOfInterval
      ⟨markedMemoryPrimeFirst A c,lt_of_le_of_lt
        (markedMemoryPrimeLifespan_nonempty line A c hc hu)
        (by have hh:=markedMemoryPrimeLast_bound A c; omega)⟩
      ⟨markedMemoryPrimeLast A c,by have hh:=markedMemoryPrimeLast_bound A c; omega⟩=c := by
  apply Prod.ext
  · cases ha : c.1 with
    | some a =>
      simp only [markedMemoryPrimeChoiceOfInterval,markedMemoryPrimeFirst,ha]
      simp
      exact Fin.ext (by dsimp; omega)
    | none =>
      by_cases hA : A.Nonempty
      · simp only [markedMemoryPrimeChoiceOfInterval,markedMemoryPrimeFirst,ha,dite_eq_left hA]
        simp
      · simp only [markedMemoryPrimeChoiceOfInterval,markedMemoryPrimeFirst,ha,dite_eq_right hA]
        simp
  · cases hb : c.2 with
    | some b =>
      simp only [markedMemoryPrimeChoiceOfInterval,markedMemoryPrimeLast,hb]
      simp
    | none =>
      have hA : A.Nonempty := by
        by_contra hn
        have hh := hc
        simp only [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hn] at hh
        rcases hh with hh | ⟨a,b,he,_,_⟩
        · exact hu.elim hn (fun hne => hne hh)
        · have hn' := congrArg Prod.snd he
          simp only [hb] at hn'
          contradiction
      simp only [markedMemoryPrimeChoiceOfInterval,markedMemoryPrimeLast,hb,dite_eq_left hA]
      simp

theorem markedMemoryPrimeChoice_interval_injective
    (b : MarkedMemoryPrimeLifespanChoice N)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hb : MarkedMemoryPrimeLifespanCompatible line A b)
    (hu : MarkedMemoryPrimeLifespanUsed A c) (hv : MarkedMemoryPrimeLifespanUsed A b)
    (hf : markedMemoryPrimeFirst A c=markedMemoryPrimeFirst A b)
    (hl : markedMemoryPrimeLast A c=markedMemoryPrimeLast A b) : c=b := by
  rw [← markedMemoryPrimeChoice_recover line A c hc hu,← markedMemoryPrimeChoice_recover line A b hb hv]
  congr 1 <;> exact Fin.ext (by assumption)

end
end ArtinMatthews
