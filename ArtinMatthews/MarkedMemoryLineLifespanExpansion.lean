module

public import ArtinMatthews.MarkedMemoryIndependentLineExpectation
public import ArtinMatthews.MarkedMemoryPrimeLifespanChoices


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite expansion of the independent-line path expectation.
Each prime contributes either no lifespan, a strict orphan pair, or one
active lifespan with optional ghost endpoints. The baseline is extracted
once per prime, and all incompatible-line contributions remain zero. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

theorem markedMemoryProjectiveFactor_lifespan_sum (p : Nat.Primes) {N : ℕ} (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)
    (A : Finset (Fin (N+1))) (hb : markedMemoryBaseline q N p≠0) :
    markedMemoryProjectiveFactor p q z hz A/markedMemoryBaseline q N p =
      ∑ c : MarkedMemoryPrimeLifespanChoice N,
        markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q N)
          (markedMemoryPositionLines p z hz) A
          (1/(((p:ℝ)+1)*markedMemoryBaseline q N p)) c := by
  by_cases hA : A.Nonempty
  · rw [markedMemoryPrimeLifespanChoiceWeight_active_sum _ _ A hA]
    have h := markedMemoryProjectiveFactor_active_normalized p q z hz A hA (V := 1) one_ne_zero hb
    simpa only [markedMemoryPrimeAtom,one_mul] using h
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    rw [he,markedMemoryPrimeLifespanChoiceWeight_empty_sum]
    have h := markedMemoryProjectiveFactor_empty_normalized p q z hz (V := 1) one_ne_zero hb
    simpa only [markedMemoryPrimeAtom,one_mul] using h

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M N : ℕ}
  (S : Finset Nat.Primes) (slots : Fin (N+1) → MarkedRawActive P M)
  (q : ℝ) (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)

def markedMemoryLineLifespanWeight (c : S → MarkedMemoryPrimeLifespanChoice N) : ℝ :=
  ∏ p : S,markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q N)
    (markedMemoryPositionLines p.1 z hz) (markedMemoryActiveVisits slots p.1)
    (1/(((p.1:ℝ)+1)*markedMemoryBaseline q N p.1)) (c p)

theorem markedMemoryIndependentLineExpectation_lifespan_sum
    (hb : ∀ p : S,markedMemoryBaseline q N p.1≠0) :
    markedMemoryIndependentLineExpectation S slots q z hz =
      (∏ p : S,markedMemoryBaseline q N p.1) *
        ∑ c : S → MarkedMemoryPrimeLifespanChoice N,markedMemoryLineLifespanWeight S slots q z hz c := by
  rw [markedMemoryIndependentLineExpectation_baseline S slots q z hz hb]
  unfold markedMemoryLineLifespanWeight
  rw [← Fintype.prod_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro p _
  exact markedMemoryProjectiveFactor_lifespan_sum p.1 q z hz _ (hb p)

end
end ArtinMatthews
