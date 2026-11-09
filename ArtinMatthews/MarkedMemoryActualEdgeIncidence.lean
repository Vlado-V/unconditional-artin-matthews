module

public import ArtinMatthews.MarkedMemoryActualEdgeOrigins
public import ArtinMatthews.MarkedMemoryLifespanSurvival


set_option backward.privateInPublic true
@[expose] public section

/-! Edge birth/death incidence is read from the actual trace endpoints.
Only its singled-out incoming active identity can be born; only the
outgoing active identity can end. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {s : MarkedRawState P (pads+1) B Z}
  (history : MarkedMemoryChronologicalHistory hZ n s)

def markedMemoryActualIncomingAt (t : ℕ) (j : J) : MarkedMemoryActualFiber hZ history j :=
  if h : t/2 < n then markedMemoryActualIncoming hZ history ⟨t/2,h⟩ j
  else markedMemoryActualActiveIds hZ history 0 j 0

def markedMemoryActualOutgoingAt (t : ℕ) (j : J) : MarkedMemoryActualFiber hZ history j :=
  if h : t/2 < n then markedMemoryActualOutgoing hZ history ⟨t/2,h⟩ j
  else markedMemoryActualActiveIds hZ history 0 j 0

theorem markedMemoryActualIncomingAt_edge (v : Fin n) (j : J) :
    markedMemoryActualIncomingAt hZ history (2*v.val+1) j = markedMemoryActualIncoming hZ history v j := by
  unfold markedMemoryActualIncomingAt
  split_ifs with h
  · have he : (⟨(2*v.val+1)/2,h⟩ : Fin n) = v := Fin.ext (by change (2*v.val+1)/2 = v.val; omega)
    rw [he]
  · have he : (2*v.val+1)/2 = v.val := by omega
    exact False.elim (h (he.symm ▸ v.2))

theorem markedMemoryActualOutgoingAt_edge (v : Fin n) (j : J) :
    markedMemoryActualOutgoingAt hZ history (2*v.val+1) j = markedMemoryActualOutgoing hZ history v j := by
  unfold markedMemoryActualOutgoingAt
  split_ifs with h
  · have he : (⟨(2*v.val+1)/2,h⟩ : Fin n) = v := Fin.ext (by change (2*v.val+1)/2 = v.val; omega)
    rw [he]
  · have he : (2*v.val+1)/2 = v.val := by omega
    exact False.elim (h (he.symm ▸ v.2))

theorem markedMemoryActualBorn_active (t : ℕ) (ho : t % 2 = 1) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) (hb : markedMemoryActualFirst hZ history j a = t+1) :
    markedMemoryActualActive hZ history (t+1) j a := by
  rcases a with ⟨addr,hgroup⟩
  cases addr with
  | inl old => change 0 = t+1 at hb; omega
  | inr b =>
    rcases b with ⟨r,b⟩
    change r+1 = t+1 at hb
    have hr : r = t := by omega
    subst r
    obtain ⟨band,k,hk⟩ := markedMemoryHistoryTrace_birth_odd hZ history t b ho
    have horigin : markedMemoryActualOrigin hZ history (t+1) (Sum.inl ⟨band,k⟩) = Sum.inr ⟨t,b⟩ := by
      change Sum.elim _ _ (markedMemoryHistoryTraceStep hZ history t (Sum.inl ⟨band,k⟩)) = _
      rw [hk]
      rfl
    have hg := markedMemoryHistoryTraceOrigin_group hZ history (t+1) (Sum.inl ⟨band,k⟩)
    have hband : band = j := (hg.symm.trans (congrArg (markedMemoryHistoryTraceAddressGroup hZ history) horigin)).trans hgroup
    subst band
    exact ⟨k,Subtype.ext horigin⟩

theorem markedMemoryActualDied_active (t : ℕ) (ht : t < 2*n+1) (ho : t % 2 = 1) (j : J)
    (a : MarkedMemoryActualFiber hZ history j) (hl : markedMemoryActualLast hZ history j a = t) :
    markedMemoryActualActive hZ history t j a := by
  have hb := (markedMemoryActual_bounds hZ history j a).1
  change markedMemoryLineageBirthTime a.1 ≤ markedMemoryHistoryLifespanLast hZ history a.1 at hb
  change markedMemoryHistoryLifespanLast hZ history a.1 = t at hl
  obtain ⟨x,hx⟩ := ((markedMemoryHistory_lifespan_exact hZ history a.1 t).mpr ⟨by omega,by omega⟩).2
  have hd : Sum.inl x ∉ Set.range (markedMemoryHistoryTraceStep hZ history t) := by
    apply (markedMemoryHistory_source_dies_iff_last hZ history t ht x).mpr
    exact (congrArg (markedMemoryHistoryLifespanLast hZ history) hx).trans hl
  obtain ⟨band,k,hk⟩ := markedMemoryHistoryTrace_death_odd hZ history t x hd ho
  subst x
  have hg := markedMemoryHistoryTraceOrigin_group hZ history t (Sum.inl ⟨band,k⟩)
  have hband : band = j := (hg.symm.trans (congrArg (markedMemoryHistoryTraceAddressGroup hZ history) hx)).trans a.2
  subst band
  exact ⟨k,Subtype.ext hx⟩

theorem markedMemoryActualEdge_birth (v : Fin n) (j : J) (a : MarkedMemoryActualFiber hZ history j)
    (hb : markedMemoryActualFirst hZ history j a = (2*v.val+1)+1) :
    a = markedMemoryActualIncoming hZ history v j := by
  have ha := markedMemoryActualBorn_active hZ history (2*v.val+1) (by omega) j a hb
  rcases (markedMemoryActualEdge_exchange hZ history v j a).mp ha with hold | hin
  · obtain ⟨k,hk⟩ := hold.1
    have hf := markedMemoryLineageOrigin_birthTime_le
      (T := MarkedMemoryHistoryTracePopulation hZ history) (Birth := MarkedMemoryHistoryTraceBirth hZ history)
      (markedMemoryHistoryTraceStep hZ history) (2*v.val+1) (Sum.inl ⟨j,k⟩)
    change markedMemoryActualFirst hZ history j (markedMemoryActualActiveIds hZ history (2*v.val+1) j k) ≤ 2*v.val+1 at hf
    rw [hk] at hf
    omega
  · exact hin

theorem markedMemoryActualEdge_death (v : Fin n) (j : J) (a : MarkedMemoryActualFiber hZ history j)
    (hl : markedMemoryActualLast hZ history j a = 2*v.val+1) :
    a = markedMemoryActualOutgoing hZ history v j := by
  have ha := markedMemoryActualDied_active hZ history (2*v.val+1) (by omega) (by omega) j a hl
  by_contra hn
  have ha' := (markedMemoryActualEdge_exchange hZ history v j a).mpr (Or.inl ⟨ha,hn⟩)
  obtain ⟨k,hk⟩ := ha'
  have hp := (markedMemoryHistory_lifespan_exact hZ history a.1 ((2*v.val+1)+1)).mp
    ⟨by omega,Sum.inl ⟨j,k⟩,congrArg Subtype.val hk⟩
  have hpLast := hp.2
  change _ ≤ markedMemoryActualLast hZ history j a at hpLast
  omega

end
end ArtinMatthews
