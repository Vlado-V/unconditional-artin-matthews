module

public import ArtinMatthews.MarkedMemoryIndependentIntervalRecover


set_option backward.privateInPublic true
@[expose] public section

/-! Every supplied independent identity is used by the recovered
one-lifespan choice. Empty initial memory excludes a first-time-zero
inactive label; local even-birth incidence excludes all other unused
labels. No support or coverage premise is added. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

omit [∀ j,DecidableEq (A j)] in
theorem markedMemoryIndependent_interval_used (hempty : ∀ j,(d.lifespan j).initial=[])
    (j : J) (a : A j) :
    MarkedMemoryPrimeLifespanUsed (markedMemoryIndependentIdentityVisits hZ d j a)
      (markedMemoryIndependentIntervalChoice hZ d j a) := by
  by_cases hV : (markedMemoryIndependentIdentityVisits hZ d j a).Nonempty
  · exact Or.inl hV
  · apply Or.inr
    intro he
    have hf : (d.lifespan j).first a%2=1 := by
      by_contra hh
      have hz : (d.lifespan j).first a%2=0 := by omega
      obtain ⟨v,hv,_⟩ := markedMemoryIndependentIdentityVisits_first_even hZ d hempty j a hz
      exact hV ⟨v,hv⟩
    have hh := congrArg Prod.fst he
    simp only [markedMemoryIndependentIntervalChoice,markedMemoryPrimeChoiceOfInterval,hf,ite_true] at hh
    contradiction

end
end ArtinMatthews
