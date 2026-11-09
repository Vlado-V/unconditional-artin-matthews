module

public import ArtinMatthews.MarkedMemoryPrimeIntervalScalar


set_option backward.privateInPublic true
@[expose] public section

/-! A strict two-ended orphan has exactly the signed birth/death pair
and the damping at its actual intermediate inactive visits. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

def markedMemoryOrphanVisitFactor (a b v : Fin (N+1)) : ℝ :=
  (if v=a then -eta a*markedLineHit line a (line a) else 1)*
    (if v=b then -eta b*markedLineHit line b (line a) else 1)*
      (if a<v ∧ v<b then markedMemoryPrimeDamping eta line a v else 1)

theorem markedMemoryPrimeIntervalVisitScalar_orphan (a b v : Fin (N+1)) (hab : a<b) :
    markedMemoryPrimeIntervalVisitScalar eta line ∅ (some a,some b) v=
      markedMemoryOrphanVisitFactor eta line a b v := by
  change
    ((if 2*a.val+1≤2*v.val ∧ 2*v.val≤2*b.val ∧ v∉(∅ : Finset (Fin (N+1))) then
        (if 2*b.val=2*v.val then -eta v*markedLineHit line v (line a)
          else 1-eta v*markedLineHit line v (line a)) else 1)*
      (if 2*a.val+1=2*v.val+1 ∧ 2*v.val+1≤2*b.val ∧ v∉(∅ : Finset (Fin (N+1))) then
        -eta v*markedLineHit line v (line a) else 1))=
      (if v=a then -eta a*markedLineHit line a (line a) else 1)*
        (if v=b then -eta b*markedLineHit line b (line a) else 1)*
          (if a<v ∧ v<b then 1-eta v*markedLineHit line v (line a) else 1)
  simp only [Finset.notMem_empty,not_false_eq_true,and_true]
  by_cases hva : v=a
  · subst v
    have hb : 2*a.val+1=2*a.val+1 ∧ 2*a.val+1≤2*b.val := by omega
    simp [hb,ne_of_lt hab]
  · by_cases hvb : v=b
    · subst v
      have hp : 2*a.val+1≤2*b.val ∧ 2*b.val≤2*b.val := by omega
      simp [hp,ne_of_gt hab]
    · have hp : (2*a.val+1≤2*v.val ∧ 2*v.val≤2*b.val) ↔ a<v ∧ v<b := by omega
      have hd : ¬2*b.val=2*v.val := by omega
      have hb : ¬(2*a.val+1=2*v.val+1 ∧ 2*v.val+1≤2*b.val) := by omega
      simp only [hp,ite_eq_right hb,ite_eq_right hva,ite_eq_right hvb,
        one_mul,mul_one]
      rw [ite_eq_right hd]


theorem markedMemoryOrphanVisitFactor_prod (a b : Fin (N+1)) (he : line a=line b) :
    (∏ v,markedMemoryOrphanVisitFactor eta line a b v)=
      eta a*eta b*(∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a))) := by
  simp only [markedMemoryOrphanVisitFactor]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  simp [Finset.prod_filter,markedMemoryPrimeDamping,markedLineHit,he]

theorem markedMemoryPrimeIntervalScalar_orphan (a b : Fin (N+1))
    (hab : a<b) (he : line a=line b) :
    markedMemoryPrimeIntervalScalar eta line ∅ (some a,some b)=
      eta a*eta b*(∏ v∈Finset.univ.filter (fun v => a<v ∧ v<b),
        (1-eta v*markedLineHit line v (line a))) := by
  unfold markedMemoryPrimeIntervalScalar
  simp_rw [markedMemoryPrimeIntervalVisitScalar_orphan eta line a b _ hab]
  exact markedMemoryOrphanVisitFactor_prod eta line a b he

end
end ArtinMatthews
