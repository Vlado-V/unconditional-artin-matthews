module

public import ArtinMatthews.MarkedMemoryCappedPathAssembly
public import ArtinMatthews.MarkedMemoryCanonicalFiber


set_option backward.privateInPublic true
@[expose] public section

/-! The capped path assembly is a concrete normalized-tableau assembly.
Consequently the frozen full-fiber extraction theorem applies to every
one of its members, retaining both ordered birth lists and copied orders. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads B n : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
  (s : MarkedRawState P (pads+1) B Z)
  (i : MarkedMemoryCappedPathDecoratedIndex (n := n) hZ s)

def markedMemoryCappedPathNormalizedIndex :
    MarkedMemoryNormalizedHistoryIndex (A := MarkedMemoryPathUsedPrime i.1.path i.1.choices) (n := n) hZ s :=
  ⟨(⟨markedMemoryCappedPathTableau (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1,
      (markedMemoryCappedPathIndependent_source hZ hP i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1).trans
        i.1.source⟩,i.2.2),
    (markedMemoryFiniteAnchorNormalize_admissible_fixed_iff hZ _).mpr
      (markedMemoryCappedPathIndependent_normalized (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1)⟩

theorem markedMemoryCappedPathNormalizedIndex_tableau :
    (markedMemoryCappedPathNormalizedIndex hZ hP s i).1.1.1=
      markedMemoryCappedPathTableau (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 := rfl

theorem markedMemoryCappedPathNormalizedIndex_assembly :
    markedMemoryNormalizedHistoryAssembly hZ s (markedMemoryCappedPathNormalizedIndex hZ hP s i)=
      markedMemoryCappedPathDecoratedAssembly hZ hP s i := rfl

theorem markedMemoryCappedPathFiber_extraction
    (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0) (H : MarkedMemoryChronologicalHistory hZ n s)
    (ha : MarkedMemoryHistoryAnchorAdmissible hZ H)
    (hi : markedMemoryCappedPathDecoratedAssembly hZ hP s i=H) :
    ∃ e : (j : J) → MarkedMemoryActualFiber hZ H j ≃ MarkedMemoryPathUsedPrime i.1.path i.1.choices j,
      markedMemoryIndependent_toFinite hZ (markedMemoryIndependentRelabel hZ e (markedMemoryActualTableau hZ H ha))=
        markedMemoryCappedPathTableau (B := B) hZ i.1.path i.1.choices i.1.compatible i.1.capacity i.2.1 ∧
      markedMemoryActualOrder hZ H ha=i.2.2 := by
  obtain ⟨e,hf,ho⟩ := markedMemoryNormalizedFiber_extraction hZ s H hempty ha
    (markedMemoryCappedPathNormalizedIndex hZ hP s i)
    ((markedMemoryCappedPathNormalizedIndex_assembly hZ hP s i).trans hi)
  exact ⟨e,hf,ho⟩

end
end ArtinMatthews
