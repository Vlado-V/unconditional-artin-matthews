module

public import ArtinMatthews.MarkedMemoryPrimeVisitFactors
public import ArtinMatthews.MarkedMemoryPrimeLifespanAnchor


set_option backward.privateInPublic true
@[expose] public section

/-! The literal half-step endpoint scalar, before any product is
partitioned into prefix/internal/suffix intervals. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

def markedMemoryPrimeIntervalVisitScalar (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (v : Fin (N+1)) : ℝ :=
  let first := markedMemoryPrimeFirst A c
  let last := markedMemoryPrimeLast A c
  let hit := markedLineHit line v (line (markedMemoryPrimeBirthVisit A c))
  (if first≤2*v.val ∧ 2*v.val≤last ∧ v∉A then
      (if last=2*v.val then -eta v*hit else 1-eta v*hit) else 1)*
    (if first=2*v.val+1 ∧ 2*v.val+1≤last ∧ v∉A then -eta v*hit else 1)

def markedMemoryPrimeIntervalScalar (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) : ℝ :=
  ∏ v,markedMemoryPrimeIntervalVisitScalar eta line A c v

theorem markedMemoryPrimeIntervalVisitScalar_active (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (hA : A.Nonempty)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (v : Fin (N+1)) :
    markedMemoryPrimeIntervalVisitScalar eta line A c v=
      markedMemoryPrefixVisitFactor eta line (A.min' hA) c.1 v*
        markedMemoryInternalVisitFactor eta line A (A.min' hA) (A.max' hA) v*
          markedMemorySuffixVisitFactor eta line (A.min' hA) (A.max' hA) c.2 v := by
  have hmin := A.min'_mem hA
  have hmax := A.max'_mem hA
  have horder := A.min'_le_max' hA
  have hc' := hc
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
  have hline := markedMemoryPrimeBirthVisit_active line A c hc (A.min' hA) hmin
  unfold markedMemoryPrimeIntervalVisitScalar
  rw [hline]
  cases ha : c.1 <;> cases hb : c.2
  all_goals
    try have hl := (hc'.2.1 _ ha).1
    try have hr := (hc'.2.2 _ hb).1
    simp only [markedMemoryPrimeFirst,markedMemoryPrimeLast,ha,hb,dite_eq_left hA,
      markedMemoryPrefixVisitFactor,markedMemoryInternalVisitFactor,markedMemorySuffixVisitFactor,
      markedMemoryPrimeDamping]
    by_cases hv : v∈A
    · have hlo := A.min'_le v hv
      have hhi := A.le_max' v hv
      simp only [hv,not_true_eq_false,and_false,ite_false]
      (try split_ifs) <;> first | omega | ring
    · have hnmin : v≠A.min' hA := by intro hh; exact hv (hh ▸ hmin)
      have hnmax : v≠A.max' hA := by intro hh; exact hv (hh ▸ hmax)
      simp only [hv,not_false_eq_true,and_true]
      (try split_ifs) <;> first | omega | (try simp_all only []; ring)

end
end ArtinMatthews
