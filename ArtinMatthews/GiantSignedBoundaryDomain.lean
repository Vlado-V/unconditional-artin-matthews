module

public import ArtinMatthews.GiantSignedProjectedWord
public import ArtinMatthews.IdealProductAverage


set_option backward.privateInPublic true
@[expose] public section

/-! The original empty-memory boundary belongs to the projected test class. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem giantSignedMemory_eq_empty_iff_degree {B : Type*} {P : B → Finset ℕ}
    (m : GiantSignedMemory P) : m = giantSignedEmptyMemory P ↔ m.1 = fun _ => 0 := by
  constructor
  · intro h
    exact congrArg Sigma.fst h
  · rcases m with ⟨d,a⟩
    intro h
    change d = (fun _ => 0) at h
    subst d
    have ha : a = fun _ i => Fin.elim0 i := by
      funext g i
      exact Fin.elim0 i
    rw [ha]
    rfl

variable {S B : Type*} [Fintype S]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedBoundary_memorySymmetric
    (s : GiantTwoSidedResidueState PS M) (a : MarkedPhysicalMarking PB M) :
    GiantSignedMemorySymmetric (fun m => giantSignedBoundary (s,a,m)) := by
  intro m σ
  have h : giantSignedMemoryPermute m σ = giantSignedEmptyMemory PB ↔
      m = giantSignedEmptyMemory PB := by
    rw [giantSignedMemory_eq_empty_iff_degree, giantSignedMemory_eq_empty_iff_degree]
    rfl
  classical
  change (if giantSignedMemoryPermute m σ = giantSignedEmptyMemory PB then (1 : ℂ) else 0) =
    if m = giantSignedEmptyMemory PB then 1 else 0
  by_cases hm : m = giantSignedEmptyMemory PB
  · rw [ite_eq_left (h.mpr hm), ite_eq_left hm]
  · rw [ite_eq_right (mt h.mp hm), ite_eq_right hm]

theorem giantSignedBoundary_activeSymmetric
    (s : GiantTwoSidedResidueState PS M) (m : GiantSignedMemory PB) :
    IdealSymmetric (fun a => giantSignedBoundary (s,a,m)) := by
  intro τ a
  rfl

theorem giantSignedStateMemoryCutoff_boundary [Fintype B] (N : ℕ) :
    giantSignedStateMemoryCutoff N (giantSignedBoundary (PS := PS) (PB := PB) (M := M)) =
      giantSignedBoundary := by
  funext s
  by_cases hm : s.2.2 = giantSignedEmptyMemory PB
  · apply giantSignedStateMemoryCutoff_of_le
    rw [hm]
    simp [giantSignedEmptyMemory]
  · have hb : giantSignedBoundary s = 0 := by simp [giantSignedBoundary, hm]
    simp only [giantSignedStateMemoryCutoff, hb, ite_self]

end
end ArtinMatthews
