module

public import Mathlib.Logic.Embedding.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Composition of indexed origins. Old identities and earlier births precede
later births; injectivity is retained independently of numeric marks. -/
namespace ArtinMatthews

def markedMemoryOriginCompose {T S R B₁ B₂ : Type*}
    (later : T ↪ S ⊕ B₂) (earlier : S ↪ R ⊕ B₁) : T ↪ R ⊕ (B₁ ⊕ B₂) :=
  (later.trans (Function.Embedding.sumMap earlier (Function.Embedding.refl _))).trans
    (Equiv.sumAssoc _ _ _).toEmbedding

/-- Numeric marks are preserved by the literal reassociation of two origin maps. -/
theorem markedMemoryOriginCompose_mark {T S R B₁ B₂ V : Type*}
    (later : T ↪ S ⊕ B₂) (earlier : S ↪ R ⊕ B₁)
    (tmark : T → V) (smark : S → V) (rmark : R → V)
    (b₁mark : B₁ → V) (b₂mark : B₂ → V)
    (hlater : ∀ i, Sum.elim smark b₂mark (later i) = tmark i)
    (hearlier : ∀ i, Sum.elim rmark b₁mark (earlier i) = smark i) (i : T) :
    Sum.elim rmark (Sum.elim b₁mark b₂mark) (markedMemoryOriginCompose later earlier i) = tmark i := by
  have hl := hlater i
  change Sum.elim rmark (Sum.elim b₁mark b₂mark)
    ((Equiv.sumAssoc R B₁ B₂) (Sum.map earlier id (later i))) = _
  generalize ho : later i = o at hl ⊢
  cases o with
  | inl old =>
    have he := hearlier old
    simp only [Sum.map_inl, Sum.elim_inl] at hl ⊢
    generalize hp : earlier old = p at he ⊢
    cases p <;> exact he.trans hl
  | inr birth => exact hl

end ArtinMatthews
