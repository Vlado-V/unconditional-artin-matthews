module

public import ArtinMatthews.MarkedMemoryGhostReconstruction
public import ArtinMatthews.MarkedMemoryEdgeReconstruction
public import ArtinMatthews.MarkedMemoryHistoryChronological


set_option backward.privateInPublic true
@[expose] public section

/-! Exact reversal from locally admissible indexed run events. Ghosts are
given by continuing old identities and ordered births; edges are given
by old-or-fresh target origins and source-last survival. Both slot
permutations remain recorded. No history correspondence is a premise. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

universe u
variable {J : Type u} [Fintype J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

abbrev MarkedMemorySlotEdgeRunData (s : MarkedRawState P (pads+1) B Z) :=
  Σ sourceSlots : MarkedMemorySlotPermutations J (pads+1),
    MarkedMemoryEdgeRunData hZ (markedRawSlotEquiv sourceSlots s) ×
      MarkedMemorySlotPermutations J (pads+1)

def markedMemorySlotEdgeRunEquiv (s : MarkedRawState P (pads+1) B Z) :
    MarkedMemoryEdgeChoice hZ s ≃ MarkedMemorySlotEdgeRunData hZ s :=
  Equiv.sigmaCongrRight (fun sourceSlots => Equiv.prodCongr
    (markedMemoryEdgeRunEquiv hZ (markedRawSlotEquiv sourceSlots s)) (Equiv.refl _))

def markedMemorySlotEdgeRunReconstruct (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemorySlotEdgeRunData hZ s) : MarkedMemoryEdgeChoice hZ s :=
  (markedMemorySlotEdgeRunEquiv hZ s).symm d

@[simp] theorem markedMemorySlotEdgeRunReconstruct_sourceSlots (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemorySlotEdgeRunData hZ s) :
    (markedMemorySlotEdgeRunReconstruct hZ s d).1 = d.1 := rfl

@[simp] theorem markedMemorySlotEdgeRunReconstruct_targetSlots (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemorySlotEdgeRunData hZ s) :
    (markedMemorySlotEdgeRunReconstruct hZ s d).2.2 = d.2.2 := rfl

def markedMemorySlotEdgeRunTarget (s : MarkedRawState P (pads+1) B Z)
    (d : MarkedMemorySlotEdgeRunData hZ s) : MarkedRawState P (pads+1) B Z :=
  markedMemoryEdgeChoiceTarget hZ s (markedMemorySlotEdgeRunReconstruct hZ s d)

/-- The next source is computed from the locally reconstructed events;
there is no supplied history, target equality, or bijection field. -/
def MarkedMemoryRunHistory : ℕ → MarkedRawState P (pads+1) B Z → Type u
  | 0,s => MarkedMemoryGhostRunData hZ s
  | n+1,s => Σ ghost : MarkedMemoryGhostRunData hZ s,
      Σ edge : MarkedMemorySlotEdgeRunData hZ
          (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)),
        MarkedMemoryRunHistory n (markedMemorySlotEdgeRunTarget hZ
          (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)) edge)

def markedMemoryRunHistoryEquiv : (n : ℕ) → (s : MarkedRawState P (pads+1) B Z) →
    MarkedMemoryChronologicalHistory hZ n s ≃ MarkedMemoryRunHistory hZ n s
  | 0,s => markedMemoryGhostRunEquiv hZ s
  | n+1,s => by
      change (Σ ghost : MarkedMemoryGhostChoice hZ s,
        Σ edge : MarkedMemoryEdgeChoice hZ (markedMemoryGhostChoiceTarget hZ s ghost),
          MarkedMemoryChronologicalHistory hZ n
            (markedMemoryEdgeChoiceTarget hZ (markedMemoryGhostChoiceTarget hZ s ghost) edge)) ≃ _
      refine (Equiv.sigmaCongrLeft' (markedMemoryGhostRunEquiv hZ s)).trans ?_
      exact Equiv.sigmaCongrRight (fun ghost =>
        (Equiv.sigmaCongrLeft' (markedMemorySlotEdgeRunEquiv hZ
          (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)))).trans
        (Equiv.sigmaCongrRight (fun edge => markedMemoryRunHistoryEquiv n
          (markedMemorySlotEdgeRunTarget hZ
            (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)) edge))))

def markedMemoryRunHistoryReconstruct {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (runs : MarkedMemoryRunHistory hZ n s) : MarkedMemoryChronologicalHistory hZ n s :=
  (markedMemoryRunHistoryEquiv hZ n s).symm runs

theorem markedMemoryRunHistory_reconstruct_encode {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryRunHistoryReconstruct hZ (markedMemoryRunHistoryEquiv hZ n s history) = history :=
  (markedMemoryRunHistoryEquiv hZ n s).symm_apply_apply history

theorem markedMemoryRunHistory_encode_reconstruct {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (runs : MarkedMemoryRunHistory hZ n s) :
    markedMemoryRunHistoryEquiv hZ n s (markedMemoryRunHistoryReconstruct hZ runs) = runs :=
  (markedMemoryRunHistoryEquiv hZ n s).apply_symm_apply runs

@[instance_reducible] def markedMemoryRunHistory_fintype [DecidableEq J]
    (n : ℕ) (s : MarkedRawState P (pads+1) B Z) : Fintype (MarkedMemoryRunHistory hZ n s) :=
  Fintype.ofEquiv (MarkedMemoryChronologicalHistory hZ n s) (markedMemoryRunHistoryEquiv hZ n s)

attribute [instance] markedMemoryRunHistory_fintype

theorem markedMemoryRunHistoryReconstruct_zero (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryGhostRunData hZ s) :
    markedMemoryRunHistoryReconstruct hZ (n := 0) ghost = markedMemoryGhostRunReconstruct hZ s ghost := rfl

theorem markedMemoryRunHistoryReconstruct_succ (n : ℕ) (s : MarkedRawState P (pads+1) B Z)
    (ghost : MarkedMemoryGhostRunData hZ s)
    (edge : MarkedMemorySlotEdgeRunData hZ
      (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)))
    (tail : MarkedMemoryRunHistory hZ n (markedMemorySlotEdgeRunTarget hZ
      (markedMemoryGhostChoiceTarget hZ s (markedMemoryGhostRunReconstruct hZ s ghost)) edge)) :
    markedMemoryRunHistoryReconstruct hZ (n := n+1) ⟨ghost,edge,tail⟩ =
      ⟨markedMemoryGhostRunReconstruct hZ s ghost,
        markedMemorySlotEdgeRunReconstruct hZ _ edge, markedMemoryRunHistoryReconstruct hZ tail⟩ := rfl

variable [DecidableEq J]

/-- Exact finite coverage: every original indexed history occurs once,
with all original tests, factorials and slot probabilities retained. -/
theorem markedMemoryRunHistory_sum (n : ℕ) (s : MarkedRawState P (pads+1) B Z)
    {T : Type*} [AddCommMonoid T]
    (F : MarkedMemoryChronologicalHistory hZ n s → T) :
    (∑ runs : MarkedMemoryRunHistory hZ n s, F (markedMemoryRunHistoryReconstruct hZ runs)) =
      ∑ history : MarkedMemoryChronologicalHistory hZ n s, F history :=
  Equiv.sum_comp (markedMemoryRunHistoryEquiv hZ n s).symm F

end
end ArtinMatthews
