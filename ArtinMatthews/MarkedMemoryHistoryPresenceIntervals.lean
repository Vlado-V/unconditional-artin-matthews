module

public import ArtinMatthews.MarkedMemoryHistoryPresence
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat


set_option backward.privateInPublic true
@[expose] public section

/-! Finite lifespan endpoints are obtained from genuine recursive lineage
membership. No lifespan bijection or interval-presence premise is used. -/
namespace ArtinMatthews
universe u v
noncomputable section

 def markedMemoryLineagePresenceTimes {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter (fun t => MarkedMemoryLineagePresent step t a)

 theorem markedMemoryLineagePresenceTimes_mem {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth) (t : ℕ) :
    t ∈ markedMemoryLineagePresenceTimes step N a ↔ t ≤ N ∧ MarkedMemoryLineagePresent step t a := by
  classical
  simp only [markedMemoryLineagePresenceTimes, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

 theorem markedMemoryLineagePresenceTimes_nonempty_iff {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth) :
    (markedMemoryLineagePresenceTimes step N a).Nonempty ↔
      ∃ t ≤ N, MarkedMemoryLineagePresent step t a := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t, (markedMemoryLineagePresenceTimes_mem step N a t).mp ht⟩
  · rintro ⟨t, htN, ht⟩
    exact ⟨t, (markedMemoryLineagePresenceTimes_mem step N a t).mpr ⟨htN, ht⟩⟩

 def markedMemoryLineageLastPresent {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) : ℕ :=
  (markedMemoryLineagePresenceTimes step N a).max' ha

 theorem markedMemoryLineageLastPresent_mem {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) :
    markedMemoryLineageLastPresent step N a ha ∈ markedMemoryLineagePresenceTimes step N a :=
  Finset.max'_mem _ ha

 theorem markedMemoryLineageLastPresent_le {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) :
    markedMemoryLineageLastPresent step N a ha ≤ N :=
  ((markedMemoryLineagePresenceTimes_mem step N a _).mp
    (markedMemoryLineageLastPresent_mem step N a ha)).1

 theorem markedMemoryLineageLastPresent_present {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) :
    MarkedMemoryLineagePresent step (markedMemoryLineageLastPresent step N a ha) a :=
  ((markedMemoryLineagePresenceTimes_mem step N a _).mp
    (markedMemoryLineageLastPresent_mem step N a ha)).2

 theorem markedMemoryLineagePresenceTimes_mem_iff_between {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) (t : ℕ) :
    t ∈ markedMemoryLineagePresenceTimes step N a ↔
      markedMemoryLineageBirthTime a ≤ t ∧ t ≤ markedMemoryLineageLastPresent step N a ha := by
  constructor
  · intro ht
    exact ⟨markedMemoryLineagePresent_birthTime_le
        ((markedMemoryLineagePresenceTimes_mem step N a t).mp ht).2,
      (markedMemoryLineagePresenceTimes step N a).le_max' t ht⟩
  · rintro ⟨hb, ht⟩
    apply (markedMemoryLineagePresenceTimes_mem step N a t).mpr
    exact ⟨ht.trans (markedMemoryLineageLastPresent_le step N a ha),
      markedMemoryLineagePresent_of_birthTime_le step a _ t hb ht
        (markedMemoryLineageLastPresent_present step N a ha)⟩

/-- The genuine finite presence set is exactly the closed integer interval
from the indexed identity's true birth time to its actual last presence. -/
 theorem markedMemoryLineagePresenceTimes_eq_Icc {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty) :
    markedMemoryLineagePresenceTimes step N a =
      Finset.Icc (markedMemoryLineageBirthTime a) (markedMemoryLineageLastPresent step N a ha) := by
  ext t
  rw [markedMemoryLineagePresenceTimes_mem_iff_between step N a ha, Finset.mem_Icc]

 theorem markedMemoryLineagePresence_finite_lifespan {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : ∃ t ≤ N, MarkedMemoryLineagePresent step t a) :
    ∃ last ≤ N, markedMemoryLineageBirthTime a ≤ last ∧
      ∀ t, (t ≤ N ∧ MarkedMemoryLineagePresent step t a) ↔
        markedMemoryLineageBirthTime a ≤ t ∧ t ≤ last := by
  have hn := (markedMemoryLineagePresenceTimes_nonempty_iff step N a).mpr ha
  refine ⟨markedMemoryLineageLastPresent step N a hn,
    markedMemoryLineageLastPresent_le step N a hn,
    markedMemoryLineagePresent_birthTime_le (markedMemoryLineageLastPresent_present step N a hn), ?_⟩
  intro t
  rw [← markedMemoryLineagePresenceTimes_mem step N a t]
  exact markedMemoryLineagePresenceTimes_mem_iff_between step N a hn t

/-- A last presence strictly before the observation horizon is a genuine
death: no later population, even beyond that horizon, can contain it. -/
 theorem markedMemoryLineage_not_present_after_last {T : ℕ → Type u} {Birth : ℕ → Type v}
    (step : ∀ t, T (t + 1) ↪ T t ⊕ Birth t) (N : ℕ)
    (a : MarkedMemoryLineageAddress T Birth)
    (ha : (markedMemoryLineagePresenceTimes step N a).Nonempty)
    (hdead : markedMemoryLineageLastPresent step N a ha < N) {t : ℕ}
    (ht : markedMemoryLineageLastPresent step N a ha < t) :
    ¬MarkedMemoryLineagePresent step t a := by
  let last := markedMemoryLineageLastPresent step N a ha
  have hnot : ¬MarkedMemoryLineagePresent step (last + 1) a := by
    intro hp
    have hmem := (markedMemoryLineagePresenceTimes_mem step N a (last + 1)).mpr
      ⟨by dsimp [last]; omega, hp⟩
    have hle := ((markedMemoryLineagePresenceTimes_mem_iff_between step N a ha (last + 1)).mp hmem).2
    dsimp [last] at hle
    omega
  exact markedMemoryLineagePresent_absent_after step
    (markedMemoryLineageLastPresent_present step N a ha) hnot (Nat.le_succ last) (by dsimp [last]; omega)

end
end ArtinMatthews
