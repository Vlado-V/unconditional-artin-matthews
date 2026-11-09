module

public import ArtinMatthews.MarkedPhysicalHistoryIndexIndependent
public import ArtinMatthews.MarkedMemoryCappedPathAssembly


set_option backward.privateInPublic true
@[expose] public section

/-! For a canonical capped prime path, the coordinate index depends only
on the original active path and its free copied ordering. All ghost-birth
enumerations and optional prime endpoints disappear from this index. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  (P : J → Finset ℕ) (hP : ∀ j p,p∈P j → p.Prime)
  (hdis : ∀ j k,j≠k → Disjoint (markedRawPrimeBand (P j)) (markedRawPrimeBand (P k)))
  {pads B R n : ℕ}
  (hZ : ∀ z∈markedPrimitiveCoordinateTube R,IsCoprime z.1 z.2)
  (s : MarkedRawState (fun j => markedRawPrimeBand (P j)) (pads+1) B (markedPrimitiveCoordinateTube R))

omit [DecidableEq J] in
theorem markedPhysicalCappedHistoryIndex_eq
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    markedPhysicalMemoryHistoryIndex P hP hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)=
      markedPhysicalActivePathIndex P hP i.1.path i.2.2 := by
  unfold markedMemoryCappedPathDecoratedAssembly
  rw [markedPhysicalMemoryHistoryIndex_transport,
    markedPhysicalMemoryHistoryIndex_independent P hP hZ _
      (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ i.1.path i.1.choices
        i.1.compatible i.1.capacity i.2.1 hdis)]
  rw [markedMemoryCappedPathIndependent_path (B := B) hZ i.1.path i.1.choices i.1.compatible
    i.1.capacity i.2.1 hdis]

omit [DecidableEq J] in
theorem markedPhysicalCappedHistory_target_position
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s) :
    (markedMemoryChronologicalTarget hZ (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)).1=
      i.1.path.position (Fin.last n) := by
  unfold markedMemoryCappedPathDecoratedAssembly
  rw [markedMemoryHistoryTransport_target,markedMemoryIndependentHistory_target]
  exact markedMemoryCappedPathIndependent_position hZ i.1.path i.1.choices i.1.compatible
    i.1.capacity i.2.1 (Fin.last n)

omit [DecidableEq J] in
theorem markedPhysicalCappedHistory_boundary
    (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s)
    (z₀ : ↥(markedPrimitiveCoordinateTube R)) :
    markedRawBoundary z₀ (markedMemoryChronologicalTarget hZ
      (markedMemoryCappedPathDecoratedAssembly hZ hdis s i))=
      if i.1.path.position (Fin.last n)=z₀ then 1 else 0 := by
  have hm : (markedMemoryChronologicalTarget hZ
      (markedMemoryCappedPathDecoratedAssembly hZ hdis s i)).2.2=markedRawBoundaryEmptyMemory _ B :=
    (markedMemoryRawMemory_empty_iff_sizes _).mpr
      (markedMemoryCappedPathDecoratedAssembly_target_empty hZ hdis s i)
  unfold markedRawBoundary
  rw [markedPhysicalCappedHistory_target_position,hm]
  simp only [and_true]

end
end ArtinMatthews
