module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite independent projective-line expectation for an
active path. Its factorization and baseline extraction retain all active
coherence conditions and all inactive damping factors. No root average
is replaced, and no physical measure is identified with the tilted one. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev MarkedMemoryIndependentLines (S : Finset Nat.Primes) :=
  (p : S) → MarkedRawPrimeLine p.1

instance markedMemoryIndependentLines_fintype (S : Finset Nat.Primes) :
    Fintype (MarkedMemoryIndependentLines S) := by infer_instance

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M N : ℕ}
  (S : Finset Nat.Primes) (slots : Fin (N+1) → MarkedRawActive P M)
  (q : ℝ) (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)

def markedMemoryPathLineFactor (p : S) (ell : MarkedRawPrimeLine p.1) : ℝ :=
  (∏ v ∈ markedMemoryActiveVisits slots p.1,
    markedLineHit (markedMemoryPositionLines p.1 z hz) v ell) *
  ∏ v ∈ Finset.univ \ markedMemoryActiveVisits slots p.1,
    (1-markedMemoryEta q N v*markedLineHit (markedMemoryPositionLines p.1 z hz) v ell)

def markedMemoryIndependentLineExpectation : ℝ :=
  (∑ ell : MarkedMemoryIndependentLines S,∏ p : S,markedMemoryPathLineFactor S slots q z hz p (ell p)) /
    (Fintype.card (MarkedMemoryIndependentLines S) : ℝ)

theorem markedMemoryIndependentLineExpectation_factorization :
    markedMemoryIndependentLineExpectation S slots q z hz=
      ∏ p : S,markedMemoryProjectiveFactor p.1 q z hz (markedMemoryActiveVisits slots p.1) := by
  unfold markedMemoryIndependentLineExpectation
  rw [← Fintype.prod_sum (fun p : S => markedMemoryPathLineFactor S slots q z hz p)]
  rw [Fintype.card_pi,Nat.cast_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rfl

theorem markedMemoryIndependentLineExpectation_baseline
    (hb : ∀ p : S,markedMemoryBaseline q N p.1≠0) :
    markedMemoryIndependentLineExpectation S slots q z hz=
      (∏ p : S,markedMemoryBaseline q N p.1) *
        ∏ p : S,markedMemoryProjectiveFactor p.1 q z hz (markedMemoryActiveVisits slots p.1) /
          markedMemoryBaseline q N p.1 := by
  rw [markedMemoryIndependentLineExpectation_factorization,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  field_simp [hb p]

theorem markedMemoryIndependentLines_card :
    Fintype.card (MarkedMemoryIndependentLines S)=∏ p : S,((p.1:ℕ)+1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p _
  exact markedMemoryPrimeLine_card p.1

end
end ArtinMatthews
