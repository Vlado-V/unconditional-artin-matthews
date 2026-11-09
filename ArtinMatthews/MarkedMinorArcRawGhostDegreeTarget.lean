module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeTransport
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeEligibility


set_option backward.privateInPublic true
@[expose] public section

/-! The canonical target is literally the survivor-then-anchored-birth
memory at its target cutoff. The deleted-hit indicator is exact. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem markedRawGhostDegreeAllowed_indicator {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) :
    (∏ j, ∏ i, if MarkedRawParticleHits (P j) z hz
      (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) i)
        then (1:ℂ) else 0)=
      if MarkedRawGhostDegreeAllowed P z hz a old then 1 else 0 := by
  classical
  by_cases h : MarkedRawGhostDegreeAllowed P z hz a old
  · have hh := (markedRawGhostDegreeAllowed_iff P z hz a old).mp h
    simp only [hh,ite_true,Finset.prod_const_one,h]
  · have hh := mt (markedRawGhostDegreeAllowed_iff P z hz a old).mpr h
    push Not at hh
    obtain ⟨j,i,hi⟩ := hh
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))

theorem markedRawGhost_degree_target {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    let c := markedRawGhostDegreeMemoryChoice P z hz a data
    markedRawGhostTargetMemory c.1 z hz c.2.1.1 c.2.2.1 c.2.2.2 =
      markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.born j) a.1.target_le
        (markedRawGhostDegreeTargetTuple P z hz a data) := by
  exact markedRawMemory_eq_of_degrees _ _ _ _
    (markedRawGhost_degree_target_sizes P z hz a data)
    (markedRawGhost_degree_target_tuple P z hz a data)

end
end ArtinMatthews
