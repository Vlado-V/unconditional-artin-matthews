module

public import ArtinMatthews.MarkedMemoryIndependentActive
public import ArtinMatthews.MarkedMemoryHistoryEdgeOriginsPopulation


set_option backward.privateInPublic true
@[expose] public section

/-! Independent interval data give injected labels on every local
population. Active labels and pending queues are disjoint by incidence,
and their union is exactly the supplied lifespan interval. Numeric
particle labels need not be injective. -/
namespace ArtinMatthews
noncomputable section

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentActive_mem (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (a : A j) :
    (d.lifespan j).active t a ↔ ∃ i, d.activeId (t/2) j i = a := by
  have hv : t/2 ≤ n := by omega
  have hc : (d.lifespan j).active t a ↔ (d.lifespan j).active (2*(t/2)) a := by
    rcases Nat.mod_two_eq_zero_or_one t with he | he
    · have heq : t = 2*(t/2) := by omega
      exact iff_of_eq (congrArg (fun s => (d.lifespan j).active s a) heq)
    · have heq : t = 2*(t/2)+1 := by omega
      exact (iff_of_eq (congrArg (fun s => (d.lifespan j).active s a) heq)).trans
        ((d.lifespan j).ghost_active (2*(t/2)) (by omega) (by omega) a)
  exact hc.trans (d.active_mem (t/2) hv j a)

omit [∀ j, DecidableEq (A j)] in
theorem markedMemoryIndependentActive_alive (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (i : Fin (pads+1)) :
    (d.lifespan j).first (d.activeId (t/2) j i) ≤ t ∧
      t ≤ (d.lifespan j).last (d.activeId (t/2) j i) := by
  have h := d.active_alive (t/2) (by omega) j i
  constructor <;> omega

def markedMemoryIndependentGroupLabel (t : ℕ) (ht : t ≤ 2*n+1) (j : J) :
    (Fin (pads+1) ⊕ Fin (markedMemoryIndependentQueue hZ d t j).length) ↪ A j where
  toFun := Sum.elim (d.activeId (t/2) j) (markedMemoryIndependentQueue hZ d t j).get
  inj' := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl ((d.activeId (t/2) j).injective hxy)
      | inr y =>
        have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) t ht _).mp (List.get_mem _ y)
        have ha := (markedMemoryIndependentActive_mem hZ d t ht j _).mpr ⟨x,hxy⟩
        exact False.elim (hm.2.2 ha)
    | inr x =>
      cases y with
      | inl y =>
        have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) t ht _).mp (List.get_mem _ x)
        have ha := (markedMemoryIndependentActive_mem hZ d t ht j _).mpr ⟨y,hxy.symm⟩
        exact False.elim (hm.2.2 ha)
      | inr y => exact congrArg Sum.inr ((markedMemoryIndependentQueue_nodup hZ d t ht j).injective_get hxy)

/-- The local population has precisely the prescribed closed interval
as its identity support. -/
theorem markedMemoryIndependentGroupLabel_range (t : ℕ) (ht : t ≤ 2*n+1) (j : J) (a : A j) :
    (∃ i, markedMemoryIndependentGroupLabel hZ d t ht j i = a) ↔
      (d.lifespan j).first a ≤ t ∧ t ≤ (d.lifespan j).last a := by
  constructor
  · rintro ⟨i,rfl⟩
    cases i with
    | inl i => exact markedMemoryIndependentActive_alive hZ d t ht j i
    | inr i =>
      exact ((markedMemoryPendingQueueAt_mem (d.lifespan j) t ht _).mp (List.get_mem _ i)).imp_right And.left
  · intro ha
    by_cases hactive : (d.lifespan j).active t a
    · obtain ⟨i,hi⟩ := (markedMemoryIndependentActive_mem hZ d t ht j a).mp hactive
      exact ⟨Sum.inl i,hi⟩
    · have hm := (markedMemoryPendingQueueAt_mem (d.lifespan j) t ht a).mpr ⟨ha.1,ha.2,hactive⟩
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
      exact ⟨Sum.inr i,hi⟩

def markedMemoryIndependentStageState (t : ℕ) (ht : t ≤ 2*n+1) : MarkedRawState P (pads+1) B Z :=
  markedMemoryIdentityRawState (fun j a => (d.particle j a).1) (d.activeId (t/2)) (d.position (t/2))
    (markedMemoryIndependentMemory hZ d t ht)

def markedMemoryIndependentPopulationLabel (t : ℕ) (ht : t ≤ 2*n+1) :
    MarkedMemoryPopulationIndex (markedMemoryIndependentStageState hZ d t ht) ↪ Σ j, A j :=
  (markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht)).toEmbedding.trans
    (Function.Embedding.sigmaMap (Function.Embedding.refl J) (markedMemoryIndependentGroupLabel hZ d t ht))

theorem markedMemoryIndependentStageState_even (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentStageState hZ d (2*v) (by omega) = markedMemoryIndependentState hZ d v hv := by
  have he : 2*v/2 = v := by omega
  dsimp only [markedMemoryIndependentStageState, markedMemoryIndependentState]
  rw [he]

theorem markedMemoryIndependentStageState_odd (v : ℕ) (hv : v ≤ n) :
    markedMemoryIndependentStageState hZ d (2*v+1) (by omega) = markedMemoryIndependentPostGhost hZ d v hv := by
  have he : (2*v+1)/2 = v := by omega
  dsimp only [markedMemoryIndependentStageState, markedMemoryIndependentPostGhost]
  rw [he]

theorem markedMemoryIndependentPopulationLabel_range (t : ℕ) (ht : t ≤ 2*n+1) (a : Σ j, A j) :
    (∃ i, markedMemoryIndependentPopulationLabel hZ d t ht i = a) ↔
      (d.lifespan a.1).first a.2 ≤ t ∧ t ≤ (d.lifespan a.1).last a.2 := by
  rcases a with ⟨j,a⟩
  constructor
  · rintro ⟨i,hi⟩
    change (Function.Embedding.sigmaMap (Function.Embedding.refl J) (markedMemoryIndependentGroupLabel hZ d t ht))
      (markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht) i) = ⟨j,a⟩ at hi
    generalize hq : markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht) i = q at hi
    rcases q with ⟨k,x⟩
    change (⟨k,markedMemoryIndependentGroupLabel hZ d t ht k x⟩ : Σ j, A j) = ⟨j,a⟩ at hi
    cases hi
    exact (markedMemoryIndependentGroupLabel_range hZ d t ht _ _).mp ⟨x,rfl⟩
  · intro ha
    obtain ⟨i,hi⟩ := (markedMemoryIndependentGroupLabel_range hZ d t ht j a).mpr ha
    refine ⟨(markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht)).symm ⟨j,i⟩, ?_⟩
    change (Function.Embedding.sigmaMap (Function.Embedding.refl J) (markedMemoryIndependentGroupLabel hZ d t ht))
      (markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht)
        ((markedMemoryPopulationGroupEquiv (markedMemoryIndependentStageState hZ d t ht)).symm ⟨j,i⟩)) = _
    rw [Equiv.apply_symm_apply]
    exact congrArg (Sigma.mk j) hi

theorem markedMemoryIndependentPopulationLabel_first_zero
    (i : MarkedMemoryPopulationIndex (markedMemoryIndependentStageState hZ d 0 (by omega))) :
    (d.lifespan (markedMemoryIndependentPopulationLabel hZ d 0 (by omega) i).1).first
      (markedMemoryIndependentPopulationLabel hZ d 0 (by omega) i).2 = 0 := by
  have h := (markedMemoryIndependentPopulationLabel_range hZ d 0 (by omega) _).mp ⟨i,rfl⟩
  omega

end
end ArtinMatthews
