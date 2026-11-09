module

public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryActivePathFinite


set_option backward.privateInPublic true
@[expose] public section

/-! A genuinely finite path-choice summation index at a fixed raw
boundary source. Only actual path fields, compatible optional endpoints
and the computed original pending capacity are stored. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)

structure MarkedMemoryCappedPathIndex where
  path : MarkedMemoryActivePathData P pads Z n
  choices : MarkedMemoryPathPrimeChoices (P := P) (n := n)
  compatible : MarkedMemoryPathChoicesCompatible path hZ choices
  capacity : MarkedMemoryPathCapacity hZ path choices compatible B
  source : markedMemoryActivePathSource (B := B) path=s

theorem markedMemoryCappedPathIndex_ext
    {a b : MarkedMemoryCappedPathIndex (n := n) hZ s}
    (hp : a.path=b.path) (hc : a.choices=b.choices) : a=b := by
  cases a
  cases b
  cases hp
  cases hc
  rfl

instance markedMemoryCappedPathIndex_finite : Finite (MarkedMemoryCappedPathIndex (n := n) hZ s) := by
  let encode := fun d : MarkedMemoryCappedPathIndex (n := n) hZ s => (d.path,d.choices)
  have hi : Function.Injective encode := by
    intro a b he
    exact markedMemoryCappedPathIndex_ext hZ s (congrArg Prod.fst he) (congrArg Prod.snd he)
  exact Finite.of_injective encode hi

instance markedMemoryCappedPathIndex_fintype : Fintype (MarkedMemoryCappedPathIndex (n := n) hZ s) :=
  Fintype.ofFinite _

abbrev MarkedMemoryCappedPathDecoratedIndex :=
  Σ i : MarkedMemoryCappedPathIndex (n := n) hZ s,
    MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ i.path i.choices i.compatible) ×
      (Fin n → J → Equiv.Perm (Fin pads))

instance markedMemoryCappedPathDecoratedIndex_fintype :
    Fintype (MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) := by infer_instance

end
end ArtinMatthews
