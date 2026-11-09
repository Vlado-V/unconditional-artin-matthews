module

public import ArtinMatthews.MarkedMemoryHistoryLifespans


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded local labels of an actual trace determine its full identity
family and the endpoints computed from that trace. No address equivalence
or endpoint equality is a premise. -/
namespace ArtinMatthews
noncomputable section
variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

structure MarkedMemoryHistoryFiniteLabels (A : Type*) where
  ids : (t : ℕ) → t ≤ 2*n+1 → MarkedMemoryHistoryTracePopulation hZ history t ↪ A
  born : (t : ℕ) → t < 2*n+1 → MarkedMemoryHistoryTraceBirth hZ history t → A
  first : A → ℕ
  last : A → ℕ
  step : ∀ t (ht : t < 2*n+1) x,
    Sum.elim (ids t (Nat.le_of_lt ht)) (born t ht)
      (markedMemoryHistoryTraceStep hZ history t x) = ids (t+1) ht x
  born_first : ∀ t (ht : t < 2*n+1) b, first (born t ht b) = t+1
  life : ∀ a, first a ≤ last a
  cap : ∀ a, last a ≤ 2*n+1
  interval : ∀ a t (ht : t ≤ 2*n+1),
    (∃ x, ids t ht x = a) ↔ first a ≤ t ∧ t ≤ last a

variable {A : Type*} (d : MarkedMemoryHistoryFiniteLabels hZ history A)

def markedMemoryHistoryFiniteLabel : MarkedMemoryHistoryTraceAddress hZ history → A :=
  Sum.elim (d.ids 0 (Nat.zero_le _)) (fun b =>
    d.born b.1 (markedMemoryHistoryTraceBirth_time_lt hZ history b.1 b.2) b.2)

theorem markedMemoryHistoryFiniteLabel_origin (t : ℕ) (ht : t ≤ 2*n+1)
    (x : MarkedMemoryHistoryTracePopulation hZ history t) :
    markedMemoryHistoryFiniteLabel hZ history d
      (markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ history) t x) = d.ids t ht x := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hlt : t < 2*n+1 := by omega
    have H := d.step t hlt x
    cases he : markedMemoryHistoryTraceStep hZ history t x with
    | inl old =>
      simp only [he, Sum.elim_inl] at H
      simpa only [markedMemoryLineageOrigin, he, Sum.elim_inl] using
        (ih (Nat.le_of_lt hlt) old).trans H
    | inr b =>
      simpa only [markedMemoryLineageOrigin, he, Sum.elim_inr,
        markedMemoryHistoryFiniteLabel] using H

theorem markedMemoryHistoryFiniteLabel_birth (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryLineageBirthTime a = d.first (markedMemoryHistoryFiniteLabel hZ history d a) := by
  cases a with
  | inl x =>
    have H := (d.interval (d.ids 0 (Nat.zero_le _) x) 0 (Nat.zero_le _)).mp ⟨x,rfl⟩
    change 0 = d.first (d.ids 0 (Nat.zero_le _) x)
    omega
  | inr b => exact (d.born_first b.1 (markedMemoryHistoryTraceBirth_time_lt hZ history b.1 b.2) b.2).symm

theorem markedMemoryHistoryFiniteLabel_injective :
    Function.Injective (markedMemoryHistoryFiniteLabel hZ history d) := by
  intro a b hab
  have htime : markedMemoryLineageBirthTime a = markedMemoryLineageBirthTime b :=
    (markedMemoryHistoryFiniteLabel_birth hZ history d a).trans
      ((congrArg d.first hab).trans (markedMemoryHistoryFiniteLabel_birth hZ history d b).symm)
  obtain ⟨ta,hta,ha⟩ := markedMemoryHistoryTraceAddress_present hZ history a
  obtain ⟨tb,_htb,hb⟩ := markedMemoryHistoryTraceAddress_present hZ history b
  have ha0 := markedMemoryLineagePresent_at_birth
    (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) ha
  have hb0 := markedMemoryLineagePresent_at_birth
    (T := MarkedMemoryHistoryTracePopulation hZ history)
    (Birth := MarkedMemoryHistoryTraceBirth hZ history) (markedMemoryHistoryTraceStep hZ history) hb
  have ht : markedMemoryLineageBirthTime a ≤ 2*n+1 :=
    (markedMemoryLineagePresent_birthTime_le
      (T := MarkedMemoryHistoryTracePopulation hZ history)
      (Birth := MarkedMemoryHistoryTraceBirth hZ history) ha).trans hta
  rw [← htime] at hb0
  obtain ⟨ia,hia⟩ := ha0
  obtain ⟨ib,hib⟩ := hb0
  have he : d.ids (markedMemoryLineageBirthTime a) ht ia =
      d.ids (markedMemoryLineageBirthTime a) ht ib :=
    (markedMemoryHistoryFiniteLabel_origin hZ history d _ ht ia).symm.trans
      ((congrArg (markedMemoryHistoryFiniteLabel hZ history d) hia).trans
        (hab.trans ((congrArg (markedMemoryHistoryFiniteLabel hZ history d) hib).symm.trans
          (markedMemoryHistoryFiniteLabel_origin hZ history d _ ht ib))))
  exact hia.symm.trans ((congrArg (markedMemoryLineageOrigin
    (markedMemoryHistoryTraceStep hZ history) _) ((d.ids _ ht).injective he)).trans hib)

theorem markedMemoryHistoryFiniteLabel_surjective :
    Function.Surjective (markedMemoryHistoryFiniteLabel hZ history d) := by
  intro a
  have ht : d.first a ≤ 2*n+1 := (d.life a).trans (d.cap a)
  obtain ⟨x,hx⟩ := (d.interval a (d.first a) ht).mpr ⟨le_rfl,d.life a⟩
  refine ⟨markedMemoryLineageOrigin (markedMemoryHistoryTraceStep hZ history) (d.first a) x, ?_⟩
  exact (markedMemoryHistoryFiniteLabel_origin hZ history d _ ht x).trans hx

def markedMemoryHistoryFiniteLabelEquiv : MarkedMemoryHistoryTraceAddress hZ history ≃ A :=
  Equiv.ofBijective (markedMemoryHistoryFiniteLabel hZ history d)
    ⟨markedMemoryHistoryFiniteLabel_injective hZ history d,
      markedMemoryHistoryFiniteLabel_surjective hZ history d⟩

theorem markedMemoryHistoryFiniteLabel_present_iff
    (a : MarkedMemoryHistoryTraceAddress hZ history) (t : ℕ) (ht : t ≤ 2*n+1) :
    MarkedMemoryLineagePresent (markedMemoryHistoryTraceStep hZ history) t a ↔
      d.first (markedMemoryHistoryFiniteLabel hZ history d a) ≤ t ∧
        t ≤ d.last (markedMemoryHistoryFiniteLabel hZ history d a) := by
  constructor
  · rintro ⟨x,hx⟩
    apply (d.interval _ t ht).mp
    exact ⟨x,(markedMemoryHistoryFiniteLabel_origin hZ history d _ ht x).symm.trans
      (congrArg (markedMemoryHistoryFiniteLabel hZ history d) hx)⟩
  · intro h
    obtain ⟨x,hx⟩ := (d.interval _ t ht).mpr h
    exact ⟨x,markedMemoryHistoryFiniteLabel_injective hZ history d
      ((markedMemoryHistoryFiniteLabel_origin hZ history d _ ht x).trans hx)⟩

theorem markedMemoryHistoryFiniteLabel_last
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryLifespanLast hZ history a = d.last (markedMemoryHistoryFiniteLabel hZ history d a) := by
  have hb := markedMemoryHistory_lifespan_bounds hZ history a
  have hp := (markedMemoryHistory_lifespan_exact hZ history a _).mpr ⟨hb.1,le_rfl⟩
  have hu := ((markedMemoryHistoryFiniteLabel_present_iff hZ history d a _ hb.2).mp hp.2).2
  have hl := (markedMemoryHistoryFiniteLabel_present_iff hZ history d a _ (d.cap _)).mpr
    ⟨d.life _,le_rfl⟩
  exact Nat.le_antisymm hu ((markedMemoryHistory_lifespan_exact hZ history a _).mp ⟨d.cap _,hl⟩).2

theorem markedMemoryHistoryFiniteLabelEquiv_birth
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryLineageBirthTime a = d.first (markedMemoryHistoryFiniteLabelEquiv hZ history d a) :=
  markedMemoryHistoryFiniteLabel_birth hZ history d a

theorem markedMemoryHistoryFiniteLabelEquiv_last
    (a : MarkedMemoryHistoryTraceAddress hZ history) :
    markedMemoryHistoryLifespanLast hZ history a = d.last (markedMemoryHistoryFiniteLabelEquiv hZ history d a) :=
  markedMemoryHistoryFiniteLabel_last hZ history d a

end
end ArtinMatthews
