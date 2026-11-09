module

public import ArtinMatthews.MarkedMemoryIndependentEndpointVisits


set_option backward.privateInPublic true
@[expose] public section

/-! The primewise ghost choice recovered from the literal independent
interval reconstructs its first and last half-step exactly. Endpoint
activity is forced by the actual empty-queue boundary conditions. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

omit [∀ j,DecidableEq (A j)] in
def markedMemoryIndependentIntervalChoice (j : J) (a : A j) : MarkedMemoryPrimeLifespanChoice n :=
  markedMemoryPrimeChoiceOfInterval
    ⟨(d.lifespan j).first a,by
      have hf := (d.lifespan j).nonempty a
      have hl := (d.lifespan j).bounded a
      omega⟩
    ⟨(d.lifespan j).last a,by have hl := (d.lifespan j).bounded a; omega⟩

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependentIntervalChoice_first
    (hempty : ∀ j,(d.lifespan j).initial=[]) (j : J) (a : A j) :
    markedMemoryPrimeFirst (markedMemoryIndependentIdentityVisits hZ d j a)
      (markedMemoryIndependentIntervalChoice hZ d j a)=(d.lifespan j).first a := by
  by_cases he : (d.lifespan j).first a%2=1
  · simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,he,ite_true,
      markedMemoryPrimeFirst]
    omega
  · have hz : (d.lifespan j).first a%2=0 := by omega
    obtain ⟨v,hv,ht⟩ := markedMemoryIndependentIdentityVisits_first_even hZ d hempty j a hz
    let V := markedMemoryIndependentIdentityVisits hZ d j a
    have hV : V.Nonempty := ⟨v,hv⟩
    have hle := Finset.min'_le V v hv
    have hmem := Finset.min'_mem V hV
    have ha := (markedMemoryIndependentIdentityVisits_alive hZ d j a (V.min' hV) hmem).1
    have hm : V.min' hV=v := Fin.ext (by change (V.min' hV).val≤v.val at hle; omega)
    simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,he,ite_false,
      markedMemoryPrimeFirst]
    change (if hA : V.Nonempty then 2*(V.min' hA).val else 0)=_
    rw [dite_eq_left hV]
    exact (congrArg (fun w : Fin (n+1) => 2*w.val) hm).trans ht.symm

theorem markedMemoryIndependentIntervalChoice_last
    (hempty : ∀ j,markedMemoryIndependentQueue hZ d (2*n+1) j=[])
    (j : J) (a : A j) :
    markedMemoryPrimeLast (markedMemoryIndependentIdentityVisits hZ d j a)
      (markedMemoryIndependentIntervalChoice hZ d j a)=(d.lifespan j).last a := by
  by_cases he : (d.lifespan j).last a%2=0
  · simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,he,ite_true,
      markedMemoryPrimeLast]
    omega
  · have hz : (d.lifespan j).last a%2=1 := by omega
    obtain ⟨v,hv,ht⟩ := markedMemoryIndependentIdentityVisits_last_odd hZ d hempty j a hz
    let V := markedMemoryIndependentIdentityVisits hZ d j a
    have hV : V.Nonempty := ⟨v,hv⟩
    have hle := Finset.le_max' V v hv
    have hmem := Finset.max'_mem V hV
    have ha := (markedMemoryIndependentIdentityVisits_alive hZ d j a (V.max' hV) hmem).2
    have hm : V.max' hV=v := Fin.ext (by change v.val≤(V.max' hV).val at hle; omega)
    simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,he,ite_false,
      markedMemoryPrimeLast]
    change (if hA : V.Nonempty then 2*(V.max' hA).val+1 else 0)=_
    rw [dite_eq_left hV]
    exact (congrArg (fun w : Fin (n+1) => 2*w.val+1) hm).trans ht.symm

end
end ArtinMatthews
