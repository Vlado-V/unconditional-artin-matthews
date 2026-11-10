module

public import Mathlib.Data.Finset.Card
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Construct pending queues from independent lifespan incidence. A
ghost removes ended identities and appends genuine births; an edge removes
the incoming identity before optionally appending the outgoing active one.
The proofs preserve indexed identities, not merely numeric prime values. -/
namespace ArtinMatthews
noncomputable section

variable {A : Type*}

def markedMemoryGhostQueue (queue born : List A) (last : A → ℕ) (t : ℕ) : List A :=
  queue.filter (fun a => decide (t < last a)) ++ born

@[simp] theorem markedMemoryGhostQueue_mem (queue born : List A) (last : A → ℕ) (t : ℕ) (a : A) :
    a ∈ markedMemoryGhostQueue queue born last t ↔ (a ∈ queue ∧ t < last a) ∨ a ∈ born := by
  simp only [markedMemoryGhostQueue, List.mem_append, List.mem_filter, decide_eq_true_eq]

theorem markedMemoryGhostQueue_nodup (queue born : List A) (first last : A → ℕ) (t : ℕ)
    (hq : queue.Nodup) (hb : born.Nodup)
    (hfirst : ∀ a ∈ queue, first a ≤ t) (hborn : ∀ a ∈ born, first a = t+1) :
    (markedMemoryGhostQueue queue born last t).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hq.filter _,hb,?_⟩
  intro a ha b hbm hab
  subst b
  have hqa := (List.mem_filter.mp ha).1
  have h₀ := hfirst a hqa
  have h₁ := hborn a hbm
  omega

/-- The ghost queue has exactly the identities alive and inactive after
the step. Genuine birth time separates the new batch from all old IDs. -/
theorem markedMemoryGhostQueue_interval (queue born : List A) (first last : A → ℕ) (t : ℕ)
    (active : A → Prop)
    (hq : ∀ a, a ∈ queue ↔ first a ≤ t ∧ t ≤ last a ∧ ¬ active a)
    (hb : ∀ a, a ∈ born ↔ first a = t+1 ∧ t+1 ≤ last a ∧ ¬ active a) (a : A) :
    a ∈ markedMemoryGhostQueue queue born last t ↔ first a ≤ t+1 ∧ t+1 ≤ last a ∧ ¬ active a := by
  rw [markedMemoryGhostQueue_mem, hq a, hb a]
  constructor
  · rintro (⟨⟨hf,hl,ha⟩,hk⟩ | ⟨hf,hl,ha⟩)
    · exact ⟨by omega,by omega,ha⟩
    · exact ⟨by omega,hl,ha⟩
  · rintro ⟨hf,hl,ha⟩
    by_cases ho : first a ≤ t
    · exact Or.inl ⟨⟨ho,by omega,ha⟩,by omega⟩
    · exact Or.inr ⟨by omega,hl,ha⟩

variable [DecidableEq A]

def markedMemoryEdgeQueue (queue : List A) (incoming outgoing : A) (store : Bool) : List A :=
  queue.filter (fun a => decide (a ≠ incoming)) ++ if store then [outgoing] else []

@[simp] theorem markedMemoryEdgeQueue_mem (queue : List A) (incoming outgoing a : A) (store : Bool) :
    a ∈ markedMemoryEdgeQueue queue incoming outgoing store ↔
      (a ∈ queue ∧ a ≠ incoming) ∨ (store = true ∧ a = outgoing) := by
  cases store <;> simp [markedMemoryEdgeQueue]

/-- Newly stored active identity was not pending before the edge; hence
the old-only promotion removal and the following store remain disjoint. -/
theorem markedMemoryEdgeQueue_nodup (queue : List A) (incoming outgoing : A) (store : Bool)
    (hq : queue.Nodup) (ho : outgoing ∉ queue) :
    (markedMemoryEdgeQueue queue incoming outgoing store).Nodup := by
  cases store with
  | false => simpa only [markedMemoryEdgeQueue, Bool.false_eq_true, ite_false, List.append_nil] using hq.filter _
  | true =>
    apply List.nodup_append.mpr
    refine ⟨hq.filter _,List.nodup_singleton _,?_⟩
    intro a ha b hb hab
    have hbo : b = outgoing := by simpa using hb
    subst b
    subst a
    exact ho (List.mem_filter.mp ha).1

/-- Under the local active-run incidence rules, the deterministic edge
queue has exactly the next alive inactive identities. -/
theorem markedMemoryEdgeQueue_interval (queue : List A) (incoming outgoing : A)
    (first last : A → ℕ) (t : ℕ) (before after : A → Prop)
    (hneq : incoming ≠ outgoing)
    (hout : before outgoing)
    (houtlife : first outgoing ≤ t ∧ t ≤ last outgoing)
    (hactive : ∀ a, after a ↔ (before a ∧ a ≠ outgoing) ∨ a = incoming)
    (hbirths : ∀ a, first a = t+1 → a = incoming)
    (hdeaths : ∀ a, last a = t → a = outgoing)
    (hq : ∀ a, a ∈ queue ↔ first a ≤ t ∧ t ≤ last a ∧ ¬ before a) (a : A) :
    a ∈ markedMemoryEdgeQueue queue incoming outgoing (decide (t < last outgoing)) ↔
      first a ≤ t+1 ∧ t+1 ≤ last a ∧ ¬ after a := by
  classical
  rw [markedMemoryEdgeQueue_mem]
  constructor
  · rintro (⟨hqa,hai⟩ | ⟨hstore,hao⟩)
    · obtain ⟨hf,hl,hnotbefore⟩ := (hq a).mp hqa
      have hao : a ≠ outgoing := by intro h; subst a; exact hnotbefore hout
      have hlast : last a ≠ t := by intro h; exact hao (hdeaths a h)
      refine ⟨by omega,by omega,?_⟩
      intro hafter
      rcases (hactive a).mp hafter with ⟨hb,_⟩ | hi
      · exact hnotbefore hb
      · exact hai hi
    · subst a
      have ht : t < last outgoing := (decide_eq_true_iff).mp hstore
      refine ⟨by omega,by omega,?_⟩
      intro hafter
      rcases (hactive outgoing).mp hafter with ⟨_,ho⟩ | hi
      · exact ho rfl
      · exact hneq hi.symm
  · rintro ⟨hf,hl,hnotafter⟩
    have hai : a ≠ incoming := by
      intro hi
      subst a
      exact hnotafter ((hactive incoming).mpr (Or.inr rfl))
    by_cases hao : a = outgoing
    · subst a
      exact Or.inr ⟨(decide_eq_true_iff).mpr (by omega),rfl⟩
    · have hnotbefore : ¬ before a := by
        intro hb
        exact hnotafter ((hactive a).mpr (Or.inl ⟨hb,hao⟩))
      have hfirst : first a ≠ t+1 := by intro h; exact hai (hbirths a h)
      exact Or.inl ⟨(hq a).mpr ⟨by omega,by omega,hnotbefore⟩,hai⟩

/-- Queue length is the pending population count once identity uniqueness
and exact incidence have been established. -/
theorem markedMemoryQueue_length_eq_card (queue : List A) (pending : Finset A)
    (hq : queue.Nodup) (hmem : ∀ a, a ∈ queue ↔ a ∈ pending) : queue.length = pending.card := by
  have he : queue.toFinset = pending := by
    ext a
    simpa only [List.mem_toFinset] using hmem a
  rw [← List.toFinset_card_of_nodup hq, he]

end
end ArtinMatthews
