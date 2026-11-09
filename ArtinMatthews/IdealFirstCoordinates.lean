module

public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.IdealPatternFreeCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! First-slot probe sets embed exactly into the full label vector.
The original free coordinates are their union with every tail slot. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealFirstEmbedding {G : Type*} {k : ℕ} (ell : ℕ) :
    (G × Fin k) ↪ (G × Fin (k+ell)) where
  toFun v := (v.1,Fin.castAdd ell v.2)
  inj' := by
    intro a b h
    have h₁ : a.1=b.1 := congrArg (fun v : G × Fin (k+ell) => v.1) h
    have h₂ : a.2=b.2 := by
      apply Fin.ext
      exact congrArg (fun v : G × Fin (k+ell) => v.2.val) h
    exact Prod.ext h₁ h₂

def idealFirstCoordinates {G : Type*} {k : ℕ} (ell : ℕ) (S : Finset (G × Fin k)) :
    Finset (G × Fin (k+ell)) := S.map (idealFirstEmbedding ell)

theorem idealFirstCoordinates_mem {G : Type*} {k ell : ℕ} (S : Finset (G × Fin k))
    (g : G) (i : Fin k) : (g,Fin.castAdd ell i)∈idealFirstCoordinates ell S ↔ (g,i)∈S :=
  show (idealFirstEmbedding (G:=G) ell (g,i))∈S.map (idealFirstEmbedding ell) ↔ (g,i)∈S from
    mem_map' (idealFirstEmbedding ell)

theorem idealFirstCoordinates_not_tail {G : Type*} {k ell : ℕ} (S : Finset (G × Fin k))
    (g : G) (i : Fin ell) : (g,Fin.natAdd k i)∉idealFirstCoordinates ell S := by
  intro h
  obtain ⟨v,_,hv⟩ := mem_map.mp h
  have he := congrArg (fun v : G × Fin (k+ell) => v.2.val) hv
  have hi := v.2.isLt
  change v.2.val=k+i.val at he
  omega

theorem idealPatternFreeCoordinates_eq {G : Type*} [Fintype G] [DecidableEq G]
    {k ell : ℕ} (S : Finset (G × Fin k)) :
    idealPatternFreeCoordinates (ell:=ell) (idealResidualFreeSlots S)=
      idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k))) ∪ idealFirstCoordinates ell S := by
  ext v
  rcases v with ⟨g,i⟩
  induction i using Fin.addCases with
  | left i =>
    simp only [idealPatternFreeCoordinates_first,mem_idealResidualFreeSlots,mem_union,
      notMem_empty,idealFirstCoordinates_mem,false_or]
  | right i =>
    simp only [idealPatternFreeCoordinates_tail,mem_union,true_or]

theorem idealPowerset_map {I J : Type*} [DecidableEq I] [DecidableEq J]
    (e : I ↪ J) (S : Finset I) :
    (S.map e).powerset=S.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  ext T
  constructor
  · intro hT
    have ht := mem_powerset.mp hT
    let A := S.filter (fun i => e i∈T)
    refine mem_map.mpr ⟨A,mem_powerset.mpr (filter_subset _ S),?_⟩
    ext j
    constructor
    · intro hj
      obtain ⟨i,hi,rfl⟩ := mem_map.mp hj
      exact (mem_filter.mp hi).2
    · intro hj
      obtain ⟨i,hi,he⟩ := mem_map.mp (ht hj)
      exact mem_map.mpr ⟨i,mem_filter.mpr ⟨hi,he.symm ▸ hj⟩,he⟩
  · intro hT
    obtain ⟨A,hA,rfl⟩ := mem_map.mp hT
    exact mem_powerset.mpr (map_subset_map.mpr (mem_powerset.mp hA))

theorem idealProbeProjection_first_coordinates {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {k ell : ℕ} (S : Finset (G × Fin k))
    (f : MarkedPhysicalMarking P (k+ell) → ℂ) :
    idealProbeProjection P (idealFirstCoordinates ell S)
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k)))) f=
      fun a => ∑ A∈S.powerset,(-1:ℂ)^A.card*
        idealAverageSet P (idealPatternFreeCoordinates (idealResidualFreeSlots A)) f a := by
  funext a
  unfold idealProbeProjection idealFirstCoordinates
  rw [idealPowerset_map,sum_map]
  apply sum_congr rfl
  intro A _
  change (-1:ℂ)^(A.map (idealFirstEmbedding ell)).card*
    idealAverageSet P
      (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k))) ∪ A.map (idealFirstEmbedding ell)) f a= _
  rw [card_map]
  change (-1:ℂ)^A.card*idealAverageSet P
    (idealPatternFreeCoordinates (fun _ : G => (∅ : Finset (Fin k))) ∪ idealFirstCoordinates ell A) f a= _
  rw [← idealPatternFreeCoordinates_eq]

end
end ArtinMatthews
