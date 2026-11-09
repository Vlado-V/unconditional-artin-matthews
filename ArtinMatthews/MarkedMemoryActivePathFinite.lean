module

public import ArtinMatthews.MarkedMemoryActivePathData


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite path carrier is finite by its bounded coordinate
tables. The exchange and physical-ban fields are propositions. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}

omit [Fintype J] in
theorem markedMemoryActivePath_ext
    {a b : MarkedMemoryActivePathData P pads Z n}
    (hp : a.position=b.position) (ha : a.active=b.active)
    (hi : a.incoming=b.incoming) (ho : a.outgoing=b.outgoing) : a=b := by
  cases a
  cases b
  cases hp
  cases ha
  cases hi
  cases ho
  rfl

instance markedMemoryActivePathData_finite : Finite (MarkedMemoryActivePathData P pads Z n) := by
  let encode := fun d : MarkedMemoryActivePathData P pads Z n =>
    (d.position,d.active,d.incoming,d.outgoing)
  have he : Function.Injective encode := by
    intro a b h
    have hh : a.position=b.position ∧ a.active=b.active ∧ a.incoming=b.incoming ∧ a.outgoing=b.outgoing := by
      simpa only [encode,Prod.mk.injEq] using h
    exact markedMemoryActivePath_ext hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  exact Finite.of_injective encode he

instance markedMemoryActivePathData_fintype : Fintype (MarkedMemoryActivePathData P pads Z n) :=
  Fintype.ofFinite _

end
end ArtinMatthews
