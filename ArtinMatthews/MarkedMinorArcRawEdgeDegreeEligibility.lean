module

public import ArtinMatthews.MarkedMinorArcRawEdgeDegreeTransport
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeEligibility
public import ArtinMatthews.MarkedMinorArcRawEdgeSlotIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! Unrestricted old-tuple and target-slot sums for the literal degree
payload. The two indicators are exactly old-hit eligibility and equality
of the selected old prime with the target slot. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem markedRawEdgeBatchOption_mem {k : ℕ} {b : Bool}
    (S : MarkedRawDeletionBatch k (markedRawEdgeBit b)) (i : Fin k) :
    i ∈ S.1 ↔ markedRawEdgeBatchOption S=some i := by
  rw [← markedRawEdgeBatchOption_toFinset S]
  simp only [Option.mem_toFinset,Option.mem_def]

def MarkedRawEdgeDegreeAllowed {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) : Prop :=
  ∀ j i, i ∈ (a.2 j).1 → MarkedRawParticleHits (P j) z hz (old j i)

def MarkedRawEdgeDegreeSlots {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (a : MarkedRawEdgeDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) (b : (j : J) → ↥(P j)) : Prop :=
  ∀ j i, i ∈ (a.2 j).1 → (old j i).1=b j

theorem markedRawEdgeDegreeAllowed_iff {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) :
    MarkedRawEdgeDegreeAllowed P z hz a old ↔
      ∀ j i, MarkedRawParticleHits (P j) z hz
        (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
          (old j) i) := by
  constructor
  · intro h j
    exact (markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j)
      (MarkedRawParticleHits (P j) z hz)).mp (h j)
  · intro h j
    exact (markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j)
      (MarkedRawParticleHits (P j) z hz)).mpr (h j)

theorem markedRawEdgeDegreeSlots_iff {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {B : ℕ} (a : MarkedRawEdgeDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) (b : (j : J) → ↥(P j)) :
    MarkedRawEdgeDegreeSlots a old b ↔
      MarkedRawEdgeRetrievedSlots (fun j i =>
        (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
          (old j) i).1) b := by
  constructor
  · intro h j
    exact (markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) (fun p => p.1=b j)).mp (h j)
  · intro h j
    exact (markedRawSubset_all_iff_deleted (a.2 j).1
      (markedRawDeletionBatch_deleted_card (a.2 j)) (old j) (fun p => p.1=b j)).mpr (h j)

def markedRawEdgeDegreePayloadEquiv {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B) :
    MarkedRawEdgeDegreePayload P z hz a ≃
      {v : ((j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
        MarkedRawParticle (P j)) × ((j : J) → ↥(P j)) //
        MarkedRawEdgeDegreeAllowed P z hz a v.1 ∧ MarkedRawEdgeDegreeSlots a v.1 v.2} where
  toFun data := ⟨(data.1.1,data.2.1),by
    constructor
    · intro j i hi
      exact data.1.2 j i ((markedRawEdgeBatchOption_mem (a.2 j) i).mp hi)
    · intro j i hi
      exact (data.2.2 j i ((markedRawEdgeBatchOption_mem (a.2 j) i).mp hi)).symm⟩
  invFun v := ⟨⟨v.1.1,by
    intro j i hi
    exact v.2.1 j i ((markedRawEdgeBatchOption_mem (a.2 j) i).mpr hi)⟩,
    ⟨v.1.2,by
      intro j i hi
      exact (v.2.2 j i ((markedRawEdgeBatchOption_mem (a.2 j) i).mpr hi)).symm⟩⟩
  left_inv := by rintro ⟨⟨old,hits⟩,⟨b,slots⟩⟩; rfl
  right_inv := by rintro ⟨⟨old,b⟩,h⟩; rfl

theorem markedRawEdge_degree_payload_sum {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B) {T : Type*} [AddCommMonoid T]
    (f : ((j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) → ((j : J) → ↥(P j)) → T) :
    (∑ data : MarkedRawEdgeDegreePayload P z hz a, f data.1.1 data.2.1)=
      ∑ old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
        MarkedRawParticle (P j), ∑ b : (j : J) → ↥(P j),
          if MarkedRawEdgeDegreeAllowed P z hz a old ∧ MarkedRawEdgeDegreeSlots a old b
          then f old b else 0 := by
  classical
  let F := fun v : ((j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
    MarkedRawParticle (P j)) × ((j : J) → ↥(P j)) => f v.1 v.2
  let good := fun v : ((j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
    MarkedRawParticle (P j)) × ((j : J) → ↥(P j)) =>
      MarkedRawEdgeDegreeAllowed P z hz a v.1 ∧ MarkedRawEdgeDegreeSlots a v.1 v.2
  calc
    _ = ∑ v : {v // good v}, F v.1 :=
      Equiv.sum_comp (markedRawEdgeDegreePayloadEquiv P z hz a) (fun v => F v.1)
    _ = ∑ v, if good v then F v else 0 := by
      rw [← Finset.sum_filter]
      exact (Finset.sum_subtype (Finset.univ.filter good) (by simp) F).symm
    _ = _ := Fintype.sum_prod_type _

theorem markedRawEdgeDegreeAllowed_indicator {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) :
    (∏ j, ∏ i, if MarkedRawParticleHits (P j) z hz
      (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
        (old j) i) then (1:ℂ) else 0)=
      if MarkedRawEdgeDegreeAllowed P z hz a old then 1 else 0 := by
  classical
  by_cases h : MarkedRawEdgeDegreeAllowed P z hz a old
  · have hh := (markedRawEdgeDegreeAllowed_iff P z hz a old).mp h
    simp only [hh,ite_true,Finset.prod_const_one,h]
  · have hh := mt (markedRawEdgeDegreeAllowed_iff P z hz a old).mpr h
    push Not at hh
    obtain ⟨j,i,hi⟩ := hh
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi))

theorem markedRawEdge_degree_payload_indicator_sum {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawEdgeDegreeShape J B)
    (f : ((j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
      MarkedRawParticle (P j)) → ((j : J) → ↥(P j)) → ℂ) :
    (∑ data : MarkedRawEdgeDegreePayload P z hz a, f data.1.1 data.2.1)=
      ∑ old : (j : J) → Fin (a.1.survivors j+markedRawEdgeBit (a.1.promoted j)) →
        MarkedRawParticle (P j), ∑ b : (j : J) → ↥(P j),
          (∏ j, ∏ i, if MarkedRawParticleHits (P j) z hz
            (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
              (old j) i) then (1:ℂ) else 0)*
          (if MarkedRawEdgeRetrievedSlots (fun j i =>
            (markedRawDeletedTupleCast (a.2 j).1 (markedRawDeletionBatch_deleted_card (a.2 j))
              (old j) i).1) b then (1:ℂ) else 0)*f old b := by
  rw [markedRawEdge_degree_payload_sum]
  apply Finset.sum_congr rfl
  intro old _
  apply Finset.sum_congr rfl
  intro b _
  rw [markedRawEdgeDegreeAllowed_indicator,← markedRawEdgeDegreeSlots_iff]
  by_cases h : MarkedRawEdgeDegreeAllowed P z hz a old <;>
    by_cases hb : MarkedRawEdgeDegreeSlots a old b <;> simp [h,hb]

end
end ArtinMatthews
