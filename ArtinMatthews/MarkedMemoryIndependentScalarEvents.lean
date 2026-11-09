module

public import ArtinMatthews.MarkedMemoryIndependentChoiceAccess
public import ArtinMatthews.MarkedMemoryHistoryLifespanScalarProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The literal scalar events of an independent tableau are its old
pending indices and ordered ghost-birth indices. Their labels and scalar
values agree with the actual reconstructed history, with all casts made
through the proved state and choice equalities. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryFinCongr {m n : ℕ} (h : m = n) : Fin m ≃ Fin n := Equiv.cast (congrArg Fin h)

theorem markedMemoryGhostSizeEq {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t) (he : HEq a b) (j : J) :
    (a.sizes.1 j : ℕ) = (b.sizes.1 j : ℕ) := by
  cases hs
  have h : a = b := eq_of_heq he
  cases h
  rfl

def markedMemoryGhostScalarEventEquiv {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t) (he : HEq a b) :
    MarkedMemoryGhostScalarEvent hZ s a ≃ MarkedMemoryGhostScalarEvent hZ t b :=
  Equiv.sumCongr
    (Equiv.sigmaCongrRight (fun j => markedMemoryFinCongr
      (congrArg (fun q : MarkedRawState P (pads+1) B Z => (q.2.2.1.1 j : ℕ)) hs)))
    (Equiv.sigmaCongrRight (fun j => markedMemoryFinCongr (markedMemoryGhostSizeEq hZ hs a b he j)))

theorem markedMemoryGhostScalarEventEquiv_value {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t) (he : HEq a b)
    (q : ℝ) (event : MarkedMemoryGhostScalarEvent hZ s a) :
    markedMemoryGhostEventScalar hZ t b q (markedMemoryGhostScalarEventEquiv hZ hs a b he event) =
      markedMemoryGhostEventScalar hZ s a q event := by
  cases hs
  have h : a = b := eq_of_heq he
  cases h
  cases event <;> rfl

theorem markedMemoryGhostBirthEquiv_heq {s t : MarkedRawState P (pads+1) B Z} (hs : s = t)
    (a : MarkedMemoryGhostChoice hZ s) (b : MarkedMemoryGhostChoice hZ t) (he : HEq a b)
    (birth : MarkedMemoryGhostBirthIndex a) :
    HEq ((Equiv.sigmaCongrRight (fun j => markedMemoryFinCongr (markedMemoryGhostSizeEq hZ hs a b he j))) birth) birth := by
  cases hs
  have h : a = b := eq_of_heq he
  cases h
  rfl

theorem markedMemoryGhostTraceBirth_heq {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (v : Fin (n+1))
    (birth : MarkedMemoryGhostBirthIndex (markedMemoryHistoryVertexGhost hZ history v)) :
    HEq (markedMemoryHistoryGhostTraceBirth hZ history v birth) birth := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    revert birth
    refine Fin.cases ?_ (fun w => ?_) v
    · intro birth; rfl
    · intro birth; exact ih history.2.2 w birth

theorem markedMemoryList_get_congr {X : Type*} {l m : List X} (h : l = m)
    (i : Fin l.length) (j : Fin m.length) (hij : i.val = j.val) : l.get i = m.get j := by
  subst m
  exact congrArg l.get (Fin.ext hij)

variable {A : J → Type*} [∀ j, DecidableEq (A j)] [∀ j, Fintype (A j)] {n : ℕ}
  (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
  (order : Fin n → J → Equiv.Perm (Fin pads))

local notation "history" => markedMemoryIndependentHistory hZ d order

abbrev MarkedMemoryIndependentGhostEventAt (v : Fin (n+1)) :=
  (Σ j : J, Fin (markedMemoryIndependentQueue hZ d (2*v.val) j).length) ⊕
    (Σ j : J, Fin ((d.lifespan j).births (2*v.val)).length)

abbrev MarkedMemoryIndependentGhostEvent := Σ v : Fin (n+1), MarkedMemoryIndependentGhostEventAt hZ d v

def markedMemoryIndependentGhostEventEquiv (v : Fin (n+1)) :
    MarkedMemoryGhostScalarEvent hZ (markedMemoryHistoryVertexState hZ history v)
      (markedMemoryHistoryVertexGhost hZ history v) ≃ MarkedMemoryIndependentGhostEventAt hZ d v :=
  markedMemoryGhostScalarEventEquiv hZ (markedMemoryIndependent_vertex_state hZ d order v)
    _ _ (markedMemoryIndependent_vertex_ghost_heq hZ d order v)

def markedMemoryIndependentScalarEventsEquiv :
    MarkedMemoryHistoryGhostScalarEvent hZ history ≃ MarkedMemoryIndependentGhostEvent hZ d :=
  Equiv.sigmaCongrRight (markedMemoryIndependentGhostEventEquiv hZ d order)

def markedMemoryIndependentGhostEventLabel (event : MarkedMemoryIndependentGhostEvent hZ d) : Σ j, A j :=
  match event.2 with
  | Sum.inl old => ⟨old.1,(markedMemoryIndependentQueue hZ d (2*event.1.val) old.1).get old.2⟩
  | Sum.inr born => ⟨born.1,((d.lifespan born.1).births (2*event.1.val)).get born.2⟩

def markedMemoryIndependentGhostEventValue (qStage : ℕ → ℝ) (offset : ℕ)
    (event : MarkedMemoryIndependentGhostEvent hZ d) : ℝ :=
  let q := qStage (offset+event.1.val)
  match event.2 with
  | Sum.inl old =>
      let a := (markedMemoryIndependentQueue hZ d (2*event.1.val) old.1).get old.2
      if (d.lifespan old.1).last a = 2*event.1.val then -(1-q)
      else if MarkedRawParticleHits (P old.1) (d.position event.1.val).1
        (hZ _ (d.position event.1.val).2) (d.particle old.1 a) then q else 1
  | Sum.inr _ => -(1-q)

theorem markedMemoryIndependentGhostEventValue_eq (qStage : ℕ → ℝ) (offset : ℕ)
    (v : Fin (n+1)) (event : MarkedMemoryIndependentGhostEventAt hZ d v) :
    markedMemoryIndependentGhostEventValue hZ d qStage offset ⟨v,event⟩ =
      markedMemoryGhostEventScalar hZ (markedMemoryIndependentState hZ d v.val (by omega))
        (markedMemoryIndependentGhost hZ d v.val (by omega)) (qStage (offset+v.val)) event := by
  cases event with
  | inl old =>
    rcases old with ⟨j,k⟩
    change _ = markedMemoryGhostOldScalar hZ (markedMemoryIndependentState hZ d v.val (by omega))
      (markedMemoryIndependentGhost hZ d v.val (by omega)) (qStage (offset+v.val)) j k
    change (if (d.lifespan j).last ((markedMemoryIndependentQueue hZ d (2*v.val) j).get k) = 2*v.val
      then -(1-qStage (offset+v.val))
      else if MarkedRawParticleHits (P j) (d.position v.val).1 (hZ _ (d.position v.val).2)
        (d.particle j ((markedMemoryIndependentQueue hZ d (2*v.val) j).get k))
        then qStage (offset+v.val) else 1) =
      (if k ∈ (Finset.univ.filter (fun i : Fin (markedMemoryIndependentQueue hZ d (2*v.val) j).length =>
          (d.lifespan j).last ((markedMemoryIndependentQueue hZ d (2*v.val) j).get i) = 2*v.val))
      then -(1-qStage (offset+v.val))
      else if k ∈ (Finset.univ.filter (fun i : Fin (markedMemoryIndependentQueue hZ d (2*v.val) j).length =>
        MarkedRawParticleHits (P j) (d.position v.val).1 (hZ _ (d.position v.val).2)
          (d.particle j ((markedMemoryIndependentQueue hZ d (2*v.val) j).get i))))
        then qStage (offset+v.val) else 1)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  | inr born => rfl

theorem markedMemoryIndependentScalarEvents_value (qStage : ℕ → ℝ) (offset : ℕ)
    (event : MarkedMemoryHistoryGhostScalarEvent hZ history) :
    markedMemoryHistoryGhostEventScalar hZ history qStage offset event =
      markedMemoryIndependentGhostEventValue hZ d qStage offset
        (markedMemoryIndependentScalarEventsEquiv hZ d order event) := by
  exact (markedMemoryGhostScalarEventEquiv_value hZ
    (markedMemoryIndependent_vertex_state hZ d order event.1) _ _
    (markedMemoryIndependent_vertex_ghost_heq hZ d order event.1)
    (qStage (offset+event.1.val)) event.2).symm.trans
      (markedMemoryIndependentGhostEventValue_eq hZ d qStage offset event.1 _).symm

end
end ArtinMatthews
