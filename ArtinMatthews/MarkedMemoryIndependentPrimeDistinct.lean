module

public import ArtinMatthews.MarkedMemoryUsedBaseline


set_option backward.privateInPublic true
@[expose] public section

/-! With empty initial memory, injective numeric labels on the actual
independent identities imply performed-birth distinctness. This is the
converse direction needed for a one-lifespan-per-prime construction. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

theorem markedMemoryIndependent_birthDistinct_of_prime_injective
    (hempty : ∀ j,(d.lifespan j).initial=[])
    (hinj : Function.Injective (markedMemoryIndependentPrime hZ d)) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order) := by
  let H := markedMemoryIndependentHistory hZ d order
  have hs : ∀ j,((markedMemoryIndependentState hZ d 0 (Nat.zero_le n)).2.2.1.1 j:ℕ)=0 := by
    intro j
    change ((markedMemoryIndependentMemory hZ d 0 (by omega)).1.1 j:ℕ)=0
    rw [markedMemory_initial_memory_empty hZ d hempty]
    rfl
  have ht : Function.Injective (markedMemoryHistoryTraceAddressPrime hZ H) := by
    intro a b hab
    apply (markedMemoryIndependentAddressEquiv hZ d order).injective
    apply hinj
    exact (markedMemoryIndependentAddress_prime hZ d order a).trans
      (hab.trans (markedMemoryIndependentAddress_prime hZ d order b).symm)
  let e := markedMemoryHistoryTraceAddressEquiv hZ H hs
  intro a b hab
  apply e.symm.injective
  apply ht
  have ha := markedMemoryHistoryTraceAddressEquiv_prime hZ H hs (e.symm a)
  have hb := markedMemoryHistoryTraceAddressEquiv_prime hZ H hs (e.symm b)
  rw [e.apply_symm_apply] at ha hb
  exact ha.symm.trans (hab.trans hb)

theorem markedMemoryIndependent_birthDistinct_iff_prime_injective
    (hempty : ∀ j,(d.lifespan j).initial=[]) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ d order) ↔
      Function.Injective (markedMemoryIndependentPrime hZ d) :=
  ⟨markedMemoryIndependentPrime_injective_of_birthDistinct hZ d order hempty,
    markedMemoryIndependent_birthDistinct_of_prime_injective hZ d order hempty⟩

end
end ArtinMatthews
