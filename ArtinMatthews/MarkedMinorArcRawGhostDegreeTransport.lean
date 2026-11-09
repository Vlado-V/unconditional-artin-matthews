module

public import ArtinMatthews.MarkedMinorArcRawGhostDegreeFibers
public import ArtinMatthews.MarkedMinorArcRawGhostHits
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeAdjoint
public import ArtinMatthews.MarkedMinorArcRawMemoryDegreeFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Literal source measure, survivor hit counts and signed ghost charges
under the exact finite degree reindexing. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_survivor_tuple_hits {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m) (j : J)
    {n : ℕ} (hn : ((del j)ᶜ).card=n) :
    markedRawTupleHitCount (P j) z hz (markedRawSurvivorTupleCast (del j) hn (m.2 j))=
      (markedRawGroupHitIndices m j z hz \ del j).card := by
  cases hn
  calc
    _ = ∑ i : Fin ((del j)ᶜ).card,
        if MarkedRawParticleHits (P j) z hz
          (markedRawSurvivorTupleCast (del j) rfl (m.2 j) i) then (1:ℕ) else 0 := by
      unfold markedRawTupleHitCount
      simp only [Finset.sum_boole,Nat.cast_id]
    _ = _ := by
      change (∑ i : Fin ((del j)ᶜ).card, if MarkedRawParticleHits (P j) z hz
        (m.2 j (((del j)ᶜ).orderEmbOfFin rfl i)) then (1:ℕ) else 0)=_
      exact markedRawGhost_survivor_hit_count m z hz del j

theorem markedRawGhost_degree_source {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    (markedRawGhostDegreeMemoryChoice P z hz a data).1=
      markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.deleted j) a.1.source_le data.1.1 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_degree_signed_coefficient {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (V : J → ℝ) (qStage ρ : ℝ) {B : ℕ}
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (a : MarkedRawGhostDegreeShape J B)
    (data : MarkedRawGhostDegreePayload P z hz a) :
    markedRawGhostSignedCoefficient V qStage ρ
      (markedRawGhostDegreeMemoryChoice P z hz a data).1 z hz
      (markedRawGhostDegreeMemoryChoice P z hz a data).2.1.1
      (markedRawGhostDegreeMemoryChoice P z hz a data).2.2.1 =
      ∏ j, (-(1-qStage)/ρ)^(a.1.deleted j)*
        (qStage/ρ^2)^(markedRawTupleHitCount (P j) z hz
          (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (data.1.1 j)))*
        (-(1-qStage)*V j/ρ)^(a.1.born j) := by
  unfold markedRawGhostSignedCoefficient
  apply Finset.prod_congr rfl
  intro j _
  have hh := markedRawGhost_survivor_tuple_hits
    (markedRawGhostDegreeMemoryChoice P z hz a data).1 z hz
    (markedRawGhostDegreeMemoryChoice P z hz a data).2.1.1 j
    (markedRawDeletionBatch_survivor_card rfl (a.2 j))
  change (-(1-qStage)/ρ)^((a.2 j).1.card)*
      (qStage/ρ^2)^((markedRawGroupHitIndices
        (markedRawGhostDegreeMemoryChoice P z hz a data).1 j z hz \ (a.2 j).1).card)*
      (-(1-qStage)*V j/ρ)^(a.1.born j)=_
  erw [markedRawDeletionBatch_deleted_card,← hh]
  rfl

def markedRawGhostDegreeTargetTuple {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    (j : J) → Fin (a.1.survivors j+a.1.born j) → MarkedRawParticle (P j) := fun j =>
  Fin.addCases
    (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (data.1.1 j))
    (fun k => markedRawAnchoredParticle (P j) (data.1.2 j k) z hz)

theorem markedRawGhost_target_tuple_cast {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (del : MarkedRawGhostDeletion m)
    (l : MarkedRawGhostBirthSizes m del) (births : MarkedRawGhostBirthLabels l) (j : J)
    {n : ℕ} (hn : ((del j)ᶜ).card=n) (i : Fin (n+(l.1 j:ℕ))) :
    (markedRawGhostTargetMemory m z hz del l births).2 j
      (Fin.cast (congrArg (fun k => k+(l.1 j:ℕ))
        (by simpa only [Finset.compl_eq_univ_sdiff,markedRawGhostSurvivors] using hn)).symm i)=
      Fin.addCases (markedRawSurvivorTupleCast (del j) hn (m.2 j))
        (fun k => markedRawAnchoredParticle (P j) (births j k) z hz) i := by
  cases hn
  rfl

theorem markedRawGhost_degree_target_sizes {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) (j : J) :
    let c := markedRawGhostDegreeMemoryChoice P z hz a data
    ((markedRawGhostTargetMemory c.1 z hz c.2.1.1 c.2.2.1 c.2.2.2).1.1 j:ℕ)=
      a.1.survivors j+a.1.born j := by
  change (Finset.univ \ (a.2 j).1).card+a.1.born j=_
  rw [← Finset.compl_eq_univ_sdiff,markedRawDeletionBatch_survivor_card rfl]

theorem markedRawGhost_degree_target_tuple {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a)
    (j : J) (i : Fin (a.1.survivors j+a.1.born j)) :
    let c := markedRawGhostDegreeMemoryChoice P z hz a data
    (markedRawGhostTargetMemory c.1 z hz c.2.1.1 c.2.2.1 c.2.2.2).2 j
      (Fin.cast (markedRawGhost_degree_target_sizes P z hz a data j).symm i)=
      markedRawGhostDegreeTargetTuple P z hz a data j i :=
  markedRawGhost_target_tuple_cast _ _ _ _ _ _ _ _ _

end
end ArtinMatthews
