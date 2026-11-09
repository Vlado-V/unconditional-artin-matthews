module

public import Mathlib.Logic.Equiv.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A finite-edge incoming-label fiber has one coordinate: the edge
vertex. This is a constructed equivalence, with the band and incoming
identity recovered from the fixed label. -/
namespace ArtinMatthews

def markedMemoryIncomingLabelFiberEquiv {I J : Type*} {A : J → Type*}
    (incoming : (i : I) → (j : J) → A j) (keep : I → J → Prop) (a : Σ j, A j) :
    {r : Σ i : I, {j : J // keep i j} //
      (⟨r.2.1,incoming r.1 r.2.1⟩ : Σ j, A j) = a} ≃
      {i : I // incoming i a.1 = a.2 ∧ keep i a.1} := by
  rcases a with ⟨j,a⟩
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨i,⟨k,hk⟩⟩,h⟩
    have hj : k = j := congrArg Sigma.fst h
    subst k
    exact ⟨i,eq_of_heq (Sigma.mk.inj h).2,hk⟩
  · intro i
    refine ⟨⟨i.1,⟨j,i.2.2⟩⟩,?_⟩
    exact Sigma.ext rfl (heq_of_eq i.2.1)
  · rintro ⟨⟨i,⟨k,hk⟩⟩,h⟩
    have hj : k = j := congrArg Sigma.fst h
    subst k
    apply Subtype.ext
    rfl
  · intro i
    apply Subtype.ext
    rfl

end ArtinMatthews
