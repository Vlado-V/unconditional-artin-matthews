module

public import ArtinMatthews.MarkedMemoryPopulationTransport


set_option backward.privateInPublic true
@[expose] public section

/-! Transport a concrete old/new identity-label equation across exact
equalities of the source, target and birth index types. -/
namespace ArtinMatthews
universe u v w z

theorem markedMemorySumLabel_transport
    {X X' : Type u} {Y Y' : Type v} {B B' : Type w} {A : Type z}
    (hX : X = X') (hY : Y = Y') (hB : B = B')
    (f : X ↪ Y ⊕ B) (g : X' ↪ Y' ⊕ B') (hf : HEq f g)
    (source : Y' → A) (born : B' → A) (target : X' → A)
    (hlabel : ∀ x, Sum.elim source born (g x) = target x) (x : X) :
    Sum.elim (fun y => source (cast hY y)) (fun b => born (cast hB b)) (f x) = target (cast hX x) := by
  cases hX
  cases hY
  cases hB
  have hfg : f = g := eq_of_heq hf
  subst g
  exact hlabel x

theorem markedMemoryDependentLabel_cast
    {I : Type u} {T : I → Type v} {A : Type w} {X : Type v}
    (label : (i : I) → T i → A) (a b : I) (h : a = b)
    (ha : X = T a) (hb : X = T b) (x : X) :
    label a (cast ha x) = label b (cast hb x) := by
  cases h
  rfl

end ArtinMatthews
