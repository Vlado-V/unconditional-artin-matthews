module

public import ArtinMatthews.MarkedMemoryPrimeOrphanScalar


set_option backward.privateInPublic true
@[expose] public section

/-! Elementwise scalar preservation between the exact one-prime line
choice and its literal half-step lifespan endpoint factors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {N : ℕ} {L : Type*} (eta : Fin (N+1) → ℝ) (line : Fin (N+1) → L)

theorem markedMemoryPrimeIntervalScalar_active (A : Finset (Fin (N+1)))
    (c : MarkedMemoryPrimeLifespanChoice N) (hA : A.Nonempty)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) :
    markedMemoryPrimeIntervalScalar eta line A c=
      markedMemoryPrefixChoice eta line (A.min' hA) c.1*
        markedMemoryInternalDamping A eta line (A.min' hA) (A.max' hA)*
          markedMemorySuffixChoice eta line (A.min' hA) (A.max' hA) c.2 := by
  have hc' := hc
  rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
  unfold markedMemoryPrimeIntervalScalar
  simp_rw [markedMemoryPrimeIntervalVisitScalar_active eta line A c hA hc]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  rw [markedMemoryPrefixVisitFactor_prod eta line _ _ (fun h hh => (hc'.2.1 h hh).1),
    markedMemoryInternalVisitFactor_prod,
    markedMemorySuffixVisitFactor_prod eta line _ _ _ (fun h hh => (hc'.2.2 h hh).1)]

theorem markedMemoryPrimeChoiceWeight_interval (A : Finset (Fin (N+1)))
    (atom : ℝ) (c : MarkedMemoryPrimeLifespanChoice N)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) :
    markedMemoryPrimeLifespanChoiceWeight eta line A atom c=
      if MarkedMemoryPrimeLifespanUsed A c then atom*markedMemoryPrimeIntervalScalar eta line A c else 1 := by
  by_cases hA : A.Nonempty
  · have hu : MarkedMemoryPrimeLifespanUsed A c := Or.inl hA
    have hc' := hc
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_left hA] at hc'
    rw [ite_eq_left hu,markedMemoryPrimeLifespanChoiceWeight,dite_eq_left hA,ite_eq_left hc'.1,
      markedMemoryPrimeIntervalScalar_active eta line A c hA hc]
  · have hE : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [MarkedMemoryPrimeLifespanCompatible,dite_eq_right Finset.not_nonempty_empty] at hc
    rcases hc with rfl | ⟨a,b,rfl,hab,he⟩
    · simp [markedMemoryPrimeLifespanChoiceWeight,markedMemoryOrphanChoice,MarkedMemoryPrimeLifespanUsed]
    · have hu : MarkedMemoryPrimeLifespanUsed (∅ : Finset (Fin (N+1))) (some a,some b) := by
        apply Or.inr
        simp
      rw [ite_eq_left hu,markedMemoryPrimeLifespanChoiceWeight,dite_eq_right Finset.not_nonempty_empty,
        markedMemoryOrphanChoice,ite_eq_left hab,ite_eq_left he,
        markedMemoryPrimeIntervalScalar_orphan eta line a b hab he]

theorem markedMemoryPrimeChoiceWeight_used_interval (A : Finset (Fin (N+1)))
    (atom : ℝ) (c : MarkedMemoryPrimeLifespanChoice N)
    (hc : MarkedMemoryPrimeLifespanCompatible line A c) (hu : MarkedMemoryPrimeLifespanUsed A c) :
    markedMemoryPrimeLifespanChoiceWeight eta line A atom c=atom*markedMemoryPrimeIntervalScalar eta line A c := by
  rw [markedMemoryPrimeChoiceWeight_interval eta line A atom c hc,ite_eq_left hu]

end
end ArtinMatthews
