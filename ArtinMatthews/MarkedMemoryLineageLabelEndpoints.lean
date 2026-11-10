module

public import ArtinMatthews.MarkedMemoryLineageLabelEquiv
public import ArtinMatthews.MarkedMemoryHistoryPresenceIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! Independent nonempty label intervals identify the endpoints computed
from genuine recursive trace occurrence.  Neither endpoint equality nor
a trace-address bijection is assumed. -/
namespace ArtinMatthews
universe u v w
noncomputable section

variable {T : ℕ → Type u} {Birth : ℕ → Type v} {A : Type w}

theorem markedMemoryLineageLabels_initial_first
    (H : ℕ) (ids : (t : ℕ) → T t ↪ A) (first last : A → ℕ)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (x : T 0) : first (ids 0 x)=0 := by
  have h := (hinterval (ids 0 x) 0 (Nat.zero_le H)).mp ⟨x,rfl⟩
  omega

theorem markedMemoryLineageLabels_cover
    (H : ℕ) (ids : (t : ℕ) → T t ↪ A) (first last : A → ℕ)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a)) :
    ∀ a, ∃ t ≤ H, ∃ x : T t, ids t x=a := by
  intro a
  have ht : first a ≤ H := (hlife a).trans (hcap a)
  exact ⟨first a,ht,(hinterval a (first a) ht).mpr ⟨le_rfl,hlife a⟩⟩

/-- Explicit realization of each new branch and nonempty bounded supplied
intervals imply that every full lineage address occurs within the horizon. -/
theorem markedMemoryLineageLabels_all_present
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hnew : ∀ t (b : Birth t), ∃ x, step t x=Sum.inr b) :
    ∀ a : MarkedMemoryLineageAddress T Birth, ∃ t ≤ H, MarkedMemoryLineagePresent step t a := by
  apply markedMemoryLineageAllPresent_of_births step H hnew
  intro t b
  calc
    t+1 = first (born t b) := (hborn t b).symm
    _ ≤ last (born t b) := hlife _
    _ ≤ H := hcap _

theorem markedMemoryLineageFiniteLabel_present_iff
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (a : MarkedMemoryLineageFiniteAddress step H) (t : ℕ) (ht : t ≤ H) :
    MarkedMemoryLineagePresent step t a.1 ↔
      ∃ x : T t, ids t x=markedMemoryLineageFiniteLabel step H ids born a := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,(markedMemoryLineageLabel_origin step ids born hstep t x).symm.trans
      (congrArg (markedMemoryLineageLabel ids born) hx)⟩
  · rintro ⟨x,hx⟩
    let b : MarkedMemoryLineageFiniteAddress step H :=
      ⟨markedMemoryLineageOrigin step t x,t,ht,x,rfl⟩
    have hab : markedMemoryLineageFiniteLabel step H ids born b=
        markedMemoryLineageFiniteLabel step H ids born a :=
      (markedMemoryLineageLabel_origin step ids born hstep t x).trans hx
    have he := markedMemoryLineageFiniteLabel_injective step H ids born first hstep hzero hborn hab
    exact ⟨x,congrArg Subtype.val he⟩

theorem markedMemoryLineageFiniteLabel_interval
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (a : MarkedMemoryLineageFiniteAddress step H) (t : ℕ) :
    (t ≤ H ∧ MarkedMemoryLineagePresent step t a.1) ↔
      first (markedMemoryLineageFiniteLabel step H ids born a) ≤ t ∧
        t ≤ last (markedMemoryLineageFiniteLabel step H ids born a) := by
  constructor
  · rintro ⟨ht,hp⟩
    exact (hinterval _ t ht).mp
      ((markedMemoryLineageFiniteLabel_present_iff step H ids born first hstep hzero hborn a t ht).mp hp)
  · intro h
    have ht : t ≤ H := h.2.trans (hcap _)
    exact ⟨ht,(markedMemoryLineageFiniteLabel_present_iff step H ids born first hstep hzero hborn a t ht).mpr
      ((hinterval _ t ht).mpr h)⟩

def markedMemoryLineageFiniteLast
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (a : MarkedMemoryLineageFiniteAddress step H) : ℕ :=
  markedMemoryLineageLastPresent step H a.1
    ((markedMemoryLineagePresenceTimes_nonempty_iff step H a.1).mpr a.2)

theorem markedMemoryLineageFiniteLabel_last
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hzero : ∀ x, first (ids 0 x)=0) (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (a : MarkedMemoryLineageFiniteAddress step H) :
    markedMemoryLineageFiniteLast step H a=last (markedMemoryLineageFiniteLabel step H ids born a) := by
  have hn := (markedMemoryLineagePresenceTimes_nonempty_iff step H a.1).mpr a.2
  have hupper : markedMemoryLineageFiniteLast step H a ≤
      last (markedMemoryLineageFiniteLabel step H ids born a) := by
    exact ((markedMemoryLineageFiniteLabel_interval step H ids born first last hstep hzero hborn hcap
      hinterval a (markedMemoryLineageFiniteLast step H a)).mp
      ⟨markedMemoryLineageLastPresent_le step H a.1 hn,
        markedMemoryLineageLastPresent_present step H a.1 hn⟩).2
  have hp := (markedMemoryLineageFiniteLabel_interval step H ids born first last hstep hzero hborn hcap
    hinterval a (last (markedMemoryLineageFiniteLabel step H ids born a))).mpr ⟨hlife _,le_rfl⟩
  have hm := (markedMemoryLineagePresenceTimes_mem step H a.1 _).mpr hp
  exact Nat.le_antisymm hupper ((markedMemoryLineagePresenceTimes step H a.1).le_max' _ hm)

def markedMemoryLineageIntervalLabelEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a)) :
    MarkedMemoryLineageFiniteAddress step H ≃ A :=
  markedMemoryLineageFiniteLabelEquiv step H ids born first hstep
    (markedMemoryLineageLabels_initial_first H ids first last hinterval) hborn
    (markedMemoryLineageLabels_cover H ids first last hlife hcap hinterval)

theorem markedMemoryLineageIntervalLabelEquiv_birth
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (a : MarkedMemoryLineageFiniteAddress step H) :
    markedMemoryLineageBirthTime a.1=
      first (markedMemoryLineageIntervalLabelEquiv step H ids born first last hstep hborn hlife hcap hinterval a) :=
  markedMemoryLineageLabel_birthTime ids born first
    (markedMemoryLineageLabels_initial_first H ids first last hinterval) hborn a.1

theorem markedMemoryLineageIntervalLabelEquiv_last
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (a : MarkedMemoryLineageFiniteAddress step H) :
    markedMemoryLineageFiniteLast step H a=
      last (markedMemoryLineageIntervalLabelEquiv step H ids born first last hstep hborn hlife hcap hinterval a) :=
  markedMemoryLineageFiniteLabel_last step H ids born first last hstep
    (markedMemoryLineageLabels_initial_first H ids first last hinterval) hborn hlife hcap hinterval a

def markedMemoryLineageIntervalFullEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth, ∃ t ≤ H, MarkedMemoryLineagePresent step t a) :
    MarkedMemoryLineageAddress T Birth ≃ A :=
  (markedMemoryLineageAddressRealizedEquiv step H hall).trans
    (markedMemoryLineageIntervalLabelEquiv step H ids born first last hstep hborn hlife hcap hinterval)

theorem markedMemoryLineageIntervalFullEquiv_birth
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth, ∃ t ≤ H, MarkedMemoryLineagePresent step t a)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageBirthTime a=
      first (markedMemoryLineageIntervalFullEquiv step H ids born first last hstep hborn hlife hcap hinterval hall a) :=
  markedMemoryLineageIntervalLabelEquiv_birth step H ids born first last hstep hborn hlife hcap hinterval ⟨a,hall a⟩

theorem markedMemoryLineageIntervalFullEquiv_last
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hall : ∀ a : MarkedMemoryLineageAddress T Birth, ∃ t ≤ H, MarkedMemoryLineagePresent step t a)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageLastPresent step H a
        ((markedMemoryLineagePresenceTimes_nonempty_iff step H a).mpr (hall a))=
      last (markedMemoryLineageIntervalFullEquiv step H ids born first last hstep hborn hlife hcap hinterval hall a) :=
  markedMemoryLineageIntervalLabelEquiv_last step H ids born first last hstep hborn hlife hcap hinterval ⟨a,hall a⟩

/-- The full address equivalence from local transition data alone. Every
new constructor is required to be an actual new branch; its finite
occurrence and all endpoint equalities are then derived. -/
def markedMemoryLineageIntervalTraceEquiv
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hnew : ∀ t (b : Birth t), ∃ x, step t x=Sum.inr b) :
    MarkedMemoryLineageAddress T Birth ≃ A :=
  markedMemoryLineageIntervalFullEquiv step H ids born first last hstep hborn hlife hcap hinterval
    (markedMemoryLineageLabels_all_present step H born first last hborn hlife hcap hnew)

theorem markedMemoryLineageIntervalTraceEquiv_birth
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hnew : ∀ t (b : Birth t), ∃ x, step t x=Sum.inr b)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageBirthTime a=
      first (markedMemoryLineageIntervalTraceEquiv step H ids born first last hstep hborn hlife hcap hinterval hnew a) :=
  markedMemoryLineageIntervalFullEquiv_birth step H ids born first last hstep hborn hlife hcap hinterval
    (markedMemoryLineageLabels_all_present step H born first last hborn hlife hcap hnew) a

theorem markedMemoryLineageIntervalTraceEquiv_last
    (step : (t : ℕ) → T (t+1) ↪ T t ⊕ Birth t) (H : ℕ)
    (ids : (t : ℕ) → T t ↪ A) (born : (t : ℕ) → Birth t → A) (first last : A → ℕ)
    (hstep : ∀ t x, Sum.elim (ids t) (born t) (step t x)=ids (t+1) x)
    (hborn : ∀ t b, first (born t b)=t+1)
    (hlife : ∀ a, first a ≤ last a) (hcap : ∀ a, last a ≤ H)
    (hinterval : ∀ a t, t ≤ H → ((∃ x : T t, ids t x=a) ↔ first a ≤ t ∧ t ≤ last a))
    (hnew : ∀ t (b : Birth t), ∃ x, step t x=Sum.inr b)
    (a : MarkedMemoryLineageAddress T Birth) :
    markedMemoryLineageLastPresent step H a
        ((markedMemoryLineagePresenceTimes_nonempty_iff step H a).mpr
          (markedMemoryLineageLabels_all_present step H born first last hborn hlife hcap hnew a))=
      last (markedMemoryLineageIntervalTraceEquiv step H ids born first last hstep hborn hlife hcap hinterval hnew a) :=
  markedMemoryLineageIntervalFullEquiv_last step H ids born first last hstep hborn hlife hcap hinterval
    (markedMemoryLineageLabels_all_present step H born first last hborn hlife hcap hnew) a

end
end ArtinMatthews
