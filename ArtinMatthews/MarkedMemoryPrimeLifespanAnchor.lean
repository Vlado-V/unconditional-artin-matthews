module

public import ArtinMatthews.MarkedMemoryPrimeLifespanInterval


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical birth vertex of every compatible primewise lifespan
supplies its fixed projective anchor at all active visits and at the
optional terminal ghost. These are proved from the literal line gates. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ}

def markedMemoryPrimeBirthVisit (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : Fin (N+1) :=
  match c.1 with
  | some a => a
  | none => if hA : A.Nonempty then A.min' hA else 0

theorem markedMemoryPrimeBirthVisit_eq_first_div (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) :
    (markedMemoryPrimeBirthVisit A c).val=markedMemoryPrimeFirst A c/2 := by
  cases ha : c.1 with
  | some a => simp only [markedMemoryPrimeBirthVisit,markedMemoryPrimeFirst,ha]; omega
  | none =>
    by_cases hA : A.Nonempty
    · simp only [markedMemoryPrimeBirthVisit,markedMemoryPrimeFirst,ha,dite_eq_left hA]
      omega
    · simp only [markedMemoryPrimeBirthVisit,markedMemoryPrimeFirst,ha,dite_eq_right hA,Fin.val_zero,Nat.zero_div]

variable {L : Type*} (line : Fin (N+1) → L)
  (A : Finset (Fin (N+1))) (c : MarkedMemoryPrimeLifespanChoice N)

theorem markedMemoryPrimeBirthVisit_active
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (v : Fin (N+1)) (hv : v∈A) :
    line (markedMemoryPrimeBirthVisit A c)=line v := by
  have hA : A.Nonempty := ⟨v,hv⟩
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc
  have hline := hc.1 v hv
  cases ha : c.1 with
  | none => simpa only [markedMemoryPrimeBirthVisit,ha,dite_eq_left hA] using hline.symm
  | some a =>
    have hp := (hc.2.1 a ha).2
    simpa only [markedMemoryPrimeBirthVisit,ha] using hp.trans hline.symm

theorem markedMemoryPrimeBirthVisit_ghost_birth
    (v : Fin (N+1)) (hf : markedMemoryPrimeFirst A c=2*v.val+1) :
    markedMemoryPrimeBirthVisit A c=v := by
  cases ha : c.1 with
  | some a =>
    simp only [markedMemoryPrimeFirst,ha] at hf
    simp only [markedMemoryPrimeBirthVisit,ha]
    exact Fin.ext (by omega)
  | none =>
    simp only [markedMemoryPrimeFirst,ha] at hf
    split_ifs at hf; omega

theorem markedMemoryPrimeBirthVisit_ghost_death
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c) (v : Fin (N+1))
    (hl : markedMemoryPrimeLast A c=2*v.val) :
    line (markedMemoryPrimeBirthVisit A c)=line v := by
  by_cases hA : A.Nonempty
  · have hc' := hc
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
    cases hb : c.2 with
    | none =>
      simp only [markedMemoryPrimeLast,hb,dite_eq_left hA] at hl
      omega
    | some b =>
      have he := (hc'.2.2 b hb).2
      simp only [markedMemoryPrimeLast,hb] at hl
      have hbv : b=v := Fin.ext (by omega)
      exact (markedMemoryPrimeBirthVisit_active line A c hc (A.min' hA) (A.min'_mem hA)).trans
        (he.symm.trans (congrArg line hbv))
  · rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA] at hc
    rcases hc with hc | ⟨a,b,rfl,_,he⟩
    · exact False.elim ((hu.resolve_left hA) hc)
    · simp only [markedMemoryPrimeLast] at hl
      have hbv : b=v := Fin.ext (by omega)
      simpa only [markedMemoryPrimeBirthVisit] using he.trans (congrArg line hbv)

theorem markedMemoryPrimeFirst_zero_active
    (hc : MarkedMemoryPrimeLifespanCompatible line A c)
    (hu : MarkedMemoryPrimeLifespanUsed A c)
    (hf : markedMemoryPrimeFirst A c=0) : (0 : Fin (N+1))∈A := by
  have hA : A.Nonempty := by
    by_contra hA
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right hA] at hc
    rcases hc with hc | ⟨a,b,rfl,_,_⟩
    · exact (hu.resolve_left hA) hc
    · simp only [markedMemoryPrimeFirst] at hf
      omega
  cases ha : c.1 with
  | some a => simp only [markedMemoryPrimeFirst,ha] at hf; omega
  | none =>
    simp only [markedMemoryPrimeFirst,ha,dite_eq_left hA] at hf
    have he : A.min' hA=(0 : Fin (N+1)) := Fin.ext (by simpa only [Fin.val_zero] using (show (A.min' hA).val=0 by omega))
    exact he ▸ A.min'_mem hA

end
end ArtinMatthews
