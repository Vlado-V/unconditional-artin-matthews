module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Tactic.Basic
public import Mathlib.Data.Nat.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Generic indexed lineage for genuine old-or-new transition injections.
Fresh identities retain their transition time; equal numeric marks play no
role. Contiguous presence is derived from the recursive origin map. -/
namespace ArtinMatthews
universe u v

abbrev MarkedMemoryLineageAddress (T : ℕ → Type u) (Birth : ℕ → Type v) :=
  T 0 ⊕ (Σ t : ℕ, Birth t)

/-- Initial particles have time zero, while a transition-t birth first
belongs to population t+1. -/
def markedMemoryLineageBirthTime {T : ℕ → Type u} {Birth : ℕ → Type v} :
    MarkedMemoryLineageAddress T Birth → ℕ
  | Sum.inl _ => 0
  | Sum.inr ⟨t, _⟩ => t + 1

/-- The actual recursive old-or-new address, without an interval premise. -/
def markedMemoryLineageOrigin {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) :
    (t : ℕ) → T t → MarkedMemoryLineageAddress T Birth
  | 0, x => Sum.inl x
  | t + 1, x => Sum.elim (markedMemoryLineageOrigin step t)
      (fun b => Sum.inr ⟨t, b⟩) (step t x)

def MarkedMemoryLineagePresent {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (t : ℕ)
    (a : MarkedMemoryLineageAddress T Birth) : Prop :=
  ∃ x, markedMemoryLineageOrigin step t x = a

 theorem markedMemoryLineageOrigin_birthTime_le {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (t : ℕ) :
    ∀ x : T t, markedMemoryLineageBirthTime (markedMemoryLineageOrigin step t x) ≤ t := by
  induction t with
  | zero => intro x; simp [markedMemoryLineageOrigin, markedMemoryLineageBirthTime]
  | succ t ih =>
    intro x
    cases hx : step t x with
    | inl old =>
      simpa only [markedMemoryLineageOrigin, hx, Sum.elim_inl] using Nat.le_trans (ih old) (Nat.le_succ t)
    | inr born => simp [markedMemoryLineageOrigin, hx, markedMemoryLineageBirthTime]

 theorem markedMemoryLineageOrigin_injective {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (t : ℕ) :
    Function.Injective (markedMemoryLineageOrigin step t) := by
  induction t with
  | zero => intro x y h; exact Sum.inl.inj h
  | succ t ih =>
    intro x y h
    apply (step t).injective
    cases hx : step t x with
    | inl oldx =>
      cases hy : step t y with
      | inl oldy =>
        simp only [markedMemoryLineageOrigin, hx, hy, Sum.elim_inl] at h
        exact congrArg Sum.inl (ih h)
      | inr newy =>
        simp only [markedMemoryLineageOrigin, hx, hy, Sum.elim_inl, Sum.elim_inr] at h
        have hb := markedMemoryLineageOrigin_birthTime_le step t oldx
        have he : markedMemoryLineageBirthTime (markedMemoryLineageOrigin step t oldx) = t + 1 :=
          congrArg markedMemoryLineageBirthTime h
        omega
    | inr newx =>
      cases hy : step t y with
      | inl oldy =>
        simp only [markedMemoryLineageOrigin, hx, hy, Sum.elim_inl, Sum.elim_inr] at h
        have hb := markedMemoryLineageOrigin_birthTime_le step t oldy
        have he : t + 1 = markedMemoryLineageBirthTime (markedMemoryLineageOrigin step t oldy) :=
          congrArg markedMemoryLineageBirthTime h
        omega
      | inr newy =>
        simp only [markedMemoryLineageOrigin, hx, hy, Sum.elim_inr] at h
        have he : newx = newy := by simpa using (Sum.inr.inj h)
        exact congrArg Sum.inr he

 theorem markedMemoryLineagePresent_birthTime_le {T : ℕ → Type u} {Birth : ℕ → Type v}
    {step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t} {t : ℕ}
    {a : MarkedMemoryLineageAddress T Birth} (ha : MarkedMemoryLineagePresent step t a) :
    markedMemoryLineageBirthTime a ≤ t := by
  obtain ⟨x, rfl⟩ := ha
  exact markedMemoryLineageOrigin_birthTime_le step t x

 theorem markedMemoryLineagePresent_predecessor_or_birth {T : ℕ → Type u} {Birth : ℕ → Type v}
    {step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t} {t : ℕ}
    {a : MarkedMemoryLineageAddress T Birth} (ha : MarkedMemoryLineagePresent step (t + 1) a) :
    MarkedMemoryLineagePresent step t a ∨ markedMemoryLineageBirthTime a = t + 1 := by
  obtain ⟨x, hx⟩ := ha
  cases hs : step t x with
  | inl old =>
    left
    exact ⟨old, by simpa only [markedMemoryLineageOrigin, hs, Sum.elim_inl] using hx⟩
  | inr born =>
    right
    have he := congrArg markedMemoryLineageBirthTime hx
    simpa only [markedMemoryLineageOrigin, hs, Sum.elim_inr, markedMemoryLineageBirthTime] using he.symm

 theorem markedMemoryLineagePresent_predecessor {T : ℕ → Type u} {Birth : ℕ → Type v}
    {step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t} {t : ℕ}
    {a : MarkedMemoryLineageAddress T Birth} (hb : markedMemoryLineageBirthTime a ≤ t)
    (ha : MarkedMemoryLineagePresent step (t + 1) a) :
    MarkedMemoryLineagePresent step t a := by
  rcases markedMemoryLineagePresent_predecessor_or_birth ha with h | h
  · exact h
  · omega

/-- Any occurrence can be traced back to every time between its actual
birth time and that occurrence. -/
 theorem markedMemoryLineagePresent_of_birthTime_le {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (a : MarkedMemoryLineageAddress T Birth) (t : ℕ) :
    ∀ s, markedMemoryLineageBirthTime a ≤ s → s ≤ t →
      MarkedMemoryLineagePresent step t a → MarkedMemoryLineagePresent step s a := by
  induction t with
  | zero =>
    intro s _ hs ha
    have h : s = 0 := by omega
    simpa only [h] using ha
  | succ t ih =>
    intro s hb hs ha
    by_cases hst : s ≤ t
    · exact ih s hb hst (markedMemoryLineagePresent_predecessor (Nat.le_trans hb hst) ha)
    · have h : s = t + 1 := by omega
      simpa only [h] using ha

/-- Indexed identities cannot disappear and later reappear. -/
 theorem markedMemoryLineagePresent_no_resurrection {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t)
    {a : MarkedMemoryLineageAddress T Birth} {r s t : ℕ}
    (hr : MarkedMemoryLineagePresent step r a) (ht : MarkedMemoryLineagePresent step t a)
    (hrs : r ≤ s) (hst : s ≤ t) : MarkedMemoryLineagePresent step s a :=
  markedMemoryLineagePresent_of_birthTime_le step a t s
    (Nat.le_trans (markedMemoryLineagePresent_birthTime_le hr) hrs) hst ht

 theorem markedMemoryLineagePresent_at_birth {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t)
    {a : MarkedMemoryLineageAddress T Birth} {t : ℕ}
    (ht : MarkedMemoryLineagePresent step t a) :
    MarkedMemoryLineagePresent step (markedMemoryLineageBirthTime a) a :=
  markedMemoryLineagePresent_of_birthTime_le step a t _ le_rfl
    (markedMemoryLineagePresent_birthTime_le ht) ht

/-- Once a previously present indexed identity is absent, it stays absent. -/
 theorem markedMemoryLineagePresent_absent_after {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t)
    {a : MarkedMemoryLineageAddress T Birth} {r s t : ℕ}
    (hr : MarkedMemoryLineagePresent step r a) (hs : ¬MarkedMemoryLineagePresent step s a)
    (hrs : r ≤ s) (hst : s ≤ t) : ¬MarkedMemoryLineagePresent step t a :=
  fun ht => hs (markedMemoryLineagePresent_no_resurrection step hr ht hrs hst)

end ArtinMatthews
