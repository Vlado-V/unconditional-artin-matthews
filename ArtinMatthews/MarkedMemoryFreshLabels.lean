module

public import ArtinMatthews.MarkedMemoryLineageLabelEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! Construct injected population labels from the initial identities and
genuine time-tagged births. Intermediate injectivity is proved, rather
than required as an input to the eventual lifespan correspondence. -/
namespace ArtinMatthews
noncomputable section

universe u v w

def MarkedMemoryBoundedLabels (S : Type u) (A : Type w) (first : A → ℕ) (t : ℕ) :=
  {e : S ↪ A // ∀ s, first (e s) ≤ t}

def markedMemoryFreshSumEmbedding {S : Type u} {B : Type v} {A : Type w}
    (first : A → ℕ) (t : ℕ) (old : MarkedMemoryBoundedLabels S A first t)
    (born : B ↪ A) (hborn : ∀ b, first (born b) = t+1) : S ⊕ B ↪ A where
  toFun := Sum.elim old.1 born
  inj' := by
    intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (old.1.injective hab)
      | inr b =>
        have he := congrArg first hab
        have ho := old.2 a
        have hn := hborn b
        change first (old.1 a) = first (born b) at he
        omega
    | inr a =>
      cases b with
      | inl b =>
        have he := congrArg first hab
        have ho := old.2 b
        have hn := hborn a
        change first (born a) = first (old.1 b) at he
        omega
      | inr b => exact congrArg Sum.inr (born.injective hab)

def markedMemoryFreshStepLabels {S : Type u} {R : Type u} {B : Type v} {A : Type w}
    (step : R ↪ S ⊕ B) (first : A → ℕ) (t : ℕ)
    (old : MarkedMemoryBoundedLabels S A first t)
    (born : B ↪ A) (hborn : ∀ b, first (born b) = t+1) :
    MarkedMemoryBoundedLabels R A first (t+1) :=
  ⟨step.trans (markedMemoryFreshSumEmbedding first t old born hborn),by
    intro x
    change first (Sum.elim old.1 born (step x)) ≤ t+1
    cases hx : step x with
    | inl y => simpa only [hx, Sum.elim_inl] using (old.2 y).trans (Nat.le_succ t)
    | inr b => simp only [Sum.elim_inr, hborn, Nat.le_refl]⟩

def markedMemoryConstructedLabels {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1) :
    (t : ℕ) → MarkedMemoryBoundedLabels (T t) A first t
  | 0 => ⟨initial,fun x => (hzero x).le⟩
  | t+1 => markedMemoryFreshStepLabels (step t) first t
      (markedMemoryConstructedLabels step first initial hzero born hborn t) (born t) (hborn t)

@[simp] theorem markedMemoryConstructedLabels_zero {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1) :
    (markedMemoryConstructedLabels step first initial hzero born hborn 0).1 = initial := rfl

theorem markedMemoryConstructedLabels_step {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1)
    (t : ℕ) (x : T (t+1)) :
    Sum.elim (markedMemoryConstructedLabels step first initial hzero born hborn t).1 (born t) (step t x) =
      (markedMemoryConstructedLabels step first initial hzero born hborn (t+1)).1 x := rfl

theorem markedMemoryConstructedLabels_injective {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1) (t : ℕ) :
    Function.Injective (markedMemoryConstructedLabels step first initial hzero born hborn t).1 :=
  (markedMemoryConstructedLabels step first initial hzero born hborn t).1.injective

theorem markedMemoryConstructedLabels_first_le {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1) (t : ℕ) (x : T t) :
    first ((markedMemoryConstructedLabels step first initial hzero born hborn t).1 x) ≤ t :=
  (markedMemoryConstructedLabels step first initial hzero born hborn t).2 x

theorem markedMemoryConstructedLabels_origin {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}
    (step : ∀ t, T (t+1) ↪ T t ⊕ Birth t) (first : A → ℕ)
    (initial : T 0 ↪ A) (hzero : ∀ x, first (initial x) = 0)
    (born : ∀ t, Birth t ↪ A) (hborn : ∀ t b, first (born t b) = t+1) (t : ℕ) (x : T t) :
    markedMemoryLineageLabel (fun t => (markedMemoryConstructedLabels step first initial hzero born hborn t).1)
      (fun t => born t) (markedMemoryLineageOrigin step t x) =
        (markedMemoryConstructedLabels step first initial hzero born hborn t).1 x :=
  markedMemoryLineageLabel_origin step _ _ (markedMemoryConstructedLabels_step step first initial hzero born hborn) t x

end
end ArtinMatthews
