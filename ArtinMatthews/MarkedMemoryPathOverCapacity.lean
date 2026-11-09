module

public import ArtinMatthews.MarkedMemoryPathOrphanCapacity


set_option backward.privateInPublic true
@[expose] public section

/-! Failure of the actual supplied pending cutoff forces many genuinely
chosen orphan primes. This keeps the source capacity unchanged. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

theorem markedMemoryPath_overCapacity_many_orphans (m : ℕ)
    (hbudget : Fintype.card J*((n+1)*(pads+1))+m≤B)
    (hbad : ¬MarkedMemoryPathCapacity hZ d c hc B) :
    m < markedMemoryPathOrphanCount d c := by
  by_contra hn
  apply hbad
  apply markedMemoryPathCapacity_of_orphan_count hZ d c hc
  exact (Nat.add_le_add_left (Nat.le_of_not_gt hn) _).trans hbudget

theorem markedMemoryPath_overCapacity_orphan_threshold (m : ℕ)
    (hbudget : Fintype.card J*((n+1)*(pads+1))+m≤B)
    (hbad : ¬MarkedMemoryPathCapacity hZ d c hc B) :
    m+1 ≤ markedMemoryPathOrphanCount d c :=
  markedMemoryPath_overCapacity_many_orphans hZ d c hc m hbudget hbad

end
end ArtinMatthews
