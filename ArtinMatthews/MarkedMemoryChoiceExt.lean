module

public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess


set_option backward.privateInPublic true
@[expose] public section

/-! Literal choice extensionality across equal raw source states. Every
non-proof coordinate is retained, including both slot permutations. -/
namespace ArtinMatthews

universe u v

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

theorem markedMemoryGhostChoice_heq_of_fields
    {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t)
    (hd : HEq a.deletion b.deletion) (hl : HEq a.sizes b.sizes) (hb : HEq a.births b.births) :
    HEq a b := by
  cases hs
  cases a with
  | mk da ha la ba =>
    cases b with
    | mk db hb lb bb =>
      have hed : da = db := eq_of_heq hd
      cases hed
      have hel : la = lb := eq_of_heq hl
      cases hel
      have heb : ba = bb := eq_of_heq hb
      cases heb
      rfl

theorem markedMemoryRawEdgeChoice_heq_of_fields
    {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedRawEdgeChoice hZ s) (b : MarkedRawEdgeChoice hZ t)
    (ht : a.target = b.target) (hst : a.store = b.store)
    (hp : HEq a.promotions b.promotions) (hf : HEq a.fresh b.fresh) : HEq a b := by
  cases hs
  cases a with
  | mk ta sa pa fa ha ba =>
    cases b with
    | mk tb sb pb fb hb bb =>
      cases ht
      cases hst
      have hep : pa = pb := eq_of_heq hp
      cases hep
      have hef : fa = fb := eq_of_heq hf
      cases hef
      rfl

theorem markedMemoryEdgeChoice_heq_of_fields
    {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryEdgeChoice hZ s) (b : MarkedMemoryEdgeChoice hZ t)
    (hσ : a.1 = b.1) (hc : HEq a.2.1 b.2.1) (hτ : a.2.2 = b.2.2) : HEq a b := by
  cases hs
  rcases a with ⟨σa,ca,τa⟩
  rcases b with ⟨σb,cb,τb⟩
  cases hσ
  have hec : ca = cb := eq_of_heq hc
  cases hec
  cases hτ
  rfl

theorem markedMemoryFunction_heq_of_cast {A B : Type u} {C : Type v} (h : A = B) (f : A → C) (g : B → C)
    (hfg : ∀ x, f x = g (cast h x)) : HEq f g := by
  cases h
  exact heq_of_eq (funext hfg)

end ArtinMatthews
