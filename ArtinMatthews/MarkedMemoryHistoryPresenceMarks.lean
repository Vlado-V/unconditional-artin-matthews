module

public import ArtinMatthews.MarkedMemoryHistoryPresence


set_option backward.privateInPublic true
@[expose] public section

/-! Actual transition marks follow the literal recursively constructed
indexed lineage; equality of numeric marks is never used for identity. -/
namespace ArtinMatthews
universe u v w

 theorem markedMemoryLineageOrigin_mark {T : ℕ → Type u} {Birth : ℕ → Type v} {V : Type w}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t)
    (mark : (t : ℕ) → T t → V) (birthMark : (t : ℕ) → Birth t → V)
    (hstep : ∀ t x, Sum.elim (mark t) (birthMark t) (step t x) = mark (t + 1) x)
    (t : ℕ) : ∀ x : T t,
    Sum.elim (mark 0) (fun b : Σ i, Birth i => birthMark b.1 b.2)
      (markedMemoryLineageOrigin step t x) = mark t x := by
  induction t with
  | zero => intro x; rfl
  | succ t ih =>
    intro x
    have hs := hstep t x
    cases hx : step t x with
    | inl old =>
      simp only [hx, Sum.elim_inl] at hs
      simpa only [markedMemoryLineageOrigin, hx, Sum.elim_inl] using (ih old).trans hs
    | inr born =>
      simpa only [markedMemoryLineageOrigin, hx, Sum.elim_inr] using hs

end ArtinMatthews
