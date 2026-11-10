module

public import ArtinMatthews.MarkedMemoryHistoryPresence
public import Mathlib.Data.Fintype.OfMap
public import Mathlib.Tactic.ToAdditive
public import ArtinMatthews.MarkedMemoryHistoryPresenceMarks


set_option backward.privateInPublic true
@[expose] public section

/-! Canonical labels of a finite genuine old-or-new trace.  Injectivity
is derived from population injections and the first time of every new
label; no identity equivalence or stored history is supplied as a premise. -/
namespace ArtinMatthews
universe u v w
noncomputable section

variable {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}

def markedMemoryLineageLabel (ids : (t : ℕ) → T t ↪ A)
    (born : (t : ℕ) → Birth t → A) : MarkedMemoryLineageAddress T Birth → A :=
  Sum.elim (ids 0) (fun b : Σ t, Birth t => born b.1 b.2)

theorem markedMemoryLineageLabel_origin
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (t : ℕ) (x : T t) :
    markedMemoryLineageLabel ids born (markedMemoryLineageOrigin step t x)=ids t x :=
  markedMemoryLineageOrigin_mark step (fun t => ids t) born hstep t x

theorem markedMemoryLineageLabel_birthTime
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageBirthTime a=first (markedMemoryLineageLabel ids born a) := by
  cases a with
  | inl x => exact (hzero x).symm
  | inr b => exact (hborn b.1 b.2).symm

/-- Two realized trace identities with the same supplied label coincide.
They are compared at their common genuine birth time. -/
theorem markedMemoryLineageLabel_injective_on_present
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    {a b : MarkedMemoryLineageAddress T Birth}
    (ha : ∃ t, MarkedMemoryLineagePresent step t a)
    (hb : ∃ t, MarkedMemoryLineagePresent step t b)
    (hab : markedMemoryLineageLabel ids born a=markedMemoryLineageLabel ids born b) : a=b := by
  have htime : markedMemoryLineageBirthTime a=markedMemoryLineageBirthTime b :=
    (markedMemoryLineageLabel_birthTime ids born first hzero hborn a).trans
      ((congrArg first hab).trans
        (markedMemoryLineageLabel_birthTime ids born first hzero hborn b).symm)
  obtain ⟨ta,ha⟩ := ha
  obtain ⟨tb,hb⟩ := hb
  have ha0 := markedMemoryLineagePresent_at_birth step ha
  have hb0 : MarkedMemoryLineagePresent step (markedMemoryLineageBirthTime a) b := by
    rw [htime]
    exact markedMemoryLineagePresent_at_birth step hb
  obtain ⟨ia,hia⟩ := ha0
  obtain ⟨ib,hib⟩ := hb0
  have hids : ids (markedMemoryLineageBirthTime a) ia=ids (markedMemoryLineageBirthTime a) ib :=
    (markedMemoryLineageLabel_origin step ids born hstep _ ia).symm.trans
      ((congrArg (markedMemoryLineageLabel ids born) hia).trans
        (hab.trans ((congrArg (markedMemoryLineageLabel ids born) hib).symm.trans
          (markedMemoryLineageLabel_origin step ids born hstep _ ib))))
  exact hia.symm.trans
    ((congrArg (markedMemoryLineageOrigin step _) ((ids _).injective hids)).trans hib)

/-- Exactly those canonical addresses that really occur before the finite
observation horizon. Unused birth constructors are excluded by occurrence. -/
abbrev MarkedMemoryLineageFiniteAddress
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ) :=
  {a : MarkedMemoryLineageAddress T Birth // ∃ t ≤ H, MarkedMemoryLineagePresent step t a}

def markedMemoryLineageFiniteLabel
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) :
    MarkedMemoryLineageFiniteAddress step H → A :=
  fun a => markedMemoryLineageLabel ids born a.1

theorem markedMemoryLineageFiniteLabel_injective
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1) :
    Function.Injective (markedMemoryLineageFiniteLabel step H ids born) := by
  intro a b hab
  apply Subtype.ext
  exact markedMemoryLineageLabel_injective_on_present step ids born first hstep hzero hborn
    ⟨a.2.choose,a.2.choose_spec.2⟩ ⟨b.2.choose,b.2.choose_spec.2⟩ hab

theorem markedMemoryLineageFiniteLabel_surjective
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a) :
    Function.Surjective (markedMemoryLineageFiniteLabel step H ids born) := by
  intro a
  obtain ⟨t,ht,x,hx⟩ := hcover a
  refine ⟨⟨markedMemoryLineageOrigin step t x,t,ht,x,rfl⟩,?_⟩
  exact (markedMemoryLineageLabel_origin step ids born hstep t x).trans hx

def markedMemoryLineageFiniteLabelEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a) :
    MarkedMemoryLineageFiniteAddress step H ≃ A :=
  Equiv.ofBijective (markedMemoryLineageFiniteLabel step H ids born)
    ⟨markedMemoryLineageFiniteLabel_injective step H ids born first hstep hzero hborn,
      markedMemoryLineageFiniteLabel_surjective step H ids born hstep hcover⟩

theorem markedMemoryLineageFiniteLabelEquiv_apply
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a)
    (a : MarkedMemoryLineageFiniteAddress step H) :
    markedMemoryLineageFiniteLabelEquiv step H ids born first hstep hzero hborn hcover a=
      markedMemoryLineageLabel ids born a.1 := rfl

@[instance_reducible] def markedMemoryLineageFiniteAddressFintype [Fintype A]
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a) :
    Fintype (MarkedMemoryLineageFiniteAddress step H) :=
  Fintype.ofEquiv A (markedMemoryLineageFiniteLabelEquiv step H ids born first hstep hzero hborn hcover).symm

/-- Every declared birth is an actual new branch of a transition, within
the horizon. This supplies occurrence of the full canonical address type. -/
theorem markedMemoryLineageAllPresent_of_births
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (hborn : ∀ t (b : Birth t), ∃ x, step t x=Sum.inr b)
    (hbound : ∀ t (_b : Birth t), t+1 ≤ H)
    (a : MarkedMemoryLineageAddress T Birth) :
    ∃ t ≤ H, MarkedMemoryLineagePresent step t a := by
  cases a with
  | inl x => exact ⟨0,Nat.zero_le _,x,rfl⟩
  | inr a =>
    obtain ⟨x,hx⟩ := hborn a.1 a.2
    refine ⟨a.1+1,hbound a.1 a.2,x,?_⟩
    simp only [markedMemoryLineageOrigin,hx,Sum.elim_inr]

def markedMemoryLineageAddressRealizedEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth,
      ∃ t ≤ H, MarkedMemoryLineagePresent step t a) :
    MarkedMemoryLineageAddress T Birth ≃ MarkedMemoryLineageFiniteAddress step H where
  toFun a := ⟨a,hall a⟩
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := rfl

def markedMemoryLineageLabelEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a)
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth,
      ∃ t ≤ H, MarkedMemoryLineagePresent step t a) :
    MarkedMemoryLineageAddress T Birth ≃ A :=
  (markedMemoryLineageAddressRealizedEquiv step H hall).trans
    (markedMemoryLineageFiniteLabelEquiv step H ids born first hstep hzero hborn hcover)

theorem markedMemoryLineageLabelEquiv_apply
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a)
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth,
      ∃ t ≤ H, MarkedMemoryLineagePresent step t a)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageLabelEquiv step H ids born first hstep hzero hborn hcover hall a=
      markedMemoryLineageLabel ids born a := rfl

theorem markedMemoryLineageLabelEquiv_origin
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcover : ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a)
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth,
      ∃ t ≤ H, MarkedMemoryLineagePresent step t a)
    (t : ℕ) (x : T t) :
    markedMemoryLineageLabelEquiv step H ids born first hstep hzero hborn hcover hall
      (markedMemoryLineageOrigin step t x)=ids t x :=
  markedMemoryLineageLabel_origin step ids born hstep t x

end
end ArtinMatthews
