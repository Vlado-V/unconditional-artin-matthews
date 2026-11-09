module

public import ArtinMatthews.MarkedPhysicalCoordinateIndexCoefficient
public import ArtinMatthews.MarkedMemoryHistoryEdgeAccess


set_option backward.privateInPublic true
@[expose] public section

/-! An actual chronological memory history determines the original
physical coordinate index: every ordered active list and both copied
slot permutations are retained. The initial coordinate remains e1. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  {s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R)}
  (H : MarkedMemoryChronologicalHistory hZ n s)

def markedPhysicalMemoryHistoryIndex : MarkedPhysicalCoordinateIndex P (pads+1) n R :=
  (fun v => markedPhysicalMarkingEquiv P hP (pads+1) (markedMemoryHistoryVertexState hZ H v).2.1,
    (fun v => (markedMemoryHistoryVertexState hZ H v.succ).1,
      fun v => ((markedMemoryHistoryVertexEdge hZ H v).1,
        fun j => ((markedMemoryHistoryVertexEdge hZ H v).2.2 j).symm)))

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_path (hs : s.1.1=(1,0)) (v : Fin (n+1)) :
    markedPhysicalCoordinateIndexPath (markedPhysicalMemoryHistoryIndex P hP hZ H).2.1 v=
      (markedMemoryHistoryVertexState hZ H v).1.1 := by
  cases v using Fin.cases with
  | zero =>
    simpa only [markedPhysicalMemoryHistoryIndex,markedPhysicalCoordinateIndexPath,Fin.cons_zero,
      markedMemoryHistoryVertexState_zero] using hs.symm
  | succ v => rfl

omit [DecidableEq J] in
theorem markedPhysicalMemoryHistoryIndex_distinct
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)
    (hd : MarkedMemoryHistoryBirthDistinct hZ H) (v : Fin (n+1)) :
    MarkedPhysicalMarkingDistinct ((markedPhysicalMemoryHistoryIndex P hP hZ H).1 v) := by
  apply (markedPhysicalMarkingEquiv_distinct P hP (pads+1) _).mpr
  intro j a b hab
  have hi := markedMemoryHistoryBirthDistinct_stage hZ H hempty hd (markedMemoryHistoryVertexStage n v)
  have he := hi (show markedMemoryPopulationPrime (markedMemoryHistoryVertexState hZ H v) (Sum.inl ⟨j,a⟩)=
    markedMemoryPopulationPrime (markedMemoryHistoryVertexState hZ H v) (Sum.inl ⟨j,b⟩) from
      congrArg (fun p => p.1) hab)
  exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj he)).2

end
end ArtinMatthews
