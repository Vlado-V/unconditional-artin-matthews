module

public import ArtinMatthews.MarkedMemoryBandPrimeEquiv
public import ArtinMatthews.MarkedMemoryLineLifespanExpansion
public import ArtinMatthews.MarkedMemoryPathOrphanTailData


set_option backward.privateInPublic true
@[expose] public section

/-! The independent uniform-line expectation on the literal union of
disjoint bands expands over the original typed path-prime choices.
Every prime baseline and every signed optional endpoint remains explicit. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) (q : ℝ)

def markedMemoryPathIndependentExpectation : ℝ :=
  markedMemoryIndependentLineExpectation (markedMemoryBandPrimeUnion P)
    (fun v j k => d.active v j k) q (fun v => (d.position v).1)
    (fun v => hZ _ (d.position v).2)

include hP

theorem markedMemoryPathIndependentExpectation_factorization :
    markedMemoryPathIndependentExpectation hZ d q=
      ∏ j,∏ p : P j,markedMemoryProjectiveFactor p.1 q (fun v => (d.position v).1)
        (fun v => hZ _ (d.position v).2) (markedMemoryPathVisits d j p) := by
  rw [markedMemoryPathIndependentExpectation,markedMemoryIndependentLineExpectation_factorization,
    ← Equiv.prod_comp (markedMemoryBandPrimeEquiv P hP),Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro p _
  change markedMemoryProjectiveFactor p.1 q _ _ (markedMemoryActiveVisits _ p.1)=_
  rw [markedMemoryActiveVisits_eq_path d hP j p]

theorem markedMemoryPathIndependentExpectation_choices
    (hb : ∀ j (p : P j),markedMemoryBaseline q n p.1≠0) :
    markedMemoryPathIndependentExpectation hZ d q=
      (∏ j,∏ p : P j,markedMemoryBaseline q n p.1)*
        ∑ c : MarkedMemoryPathPrimeChoices (P := P) (n := n),markedMemoryPathPrimeChoiceWeight hZ d q c := by
  rw [markedMemoryPathIndependentExpectation_factorization hZ d hP q]
  have hp (j : J) (p : P j) :
      markedMemoryProjectiveFactor p.1 q (fun v => (d.position v).1) (fun v => hZ _ (d.position v).2)
        (markedMemoryPathVisits d j p)=markedMemoryBaseline q n p.1*
          ∑ c : MarkedMemoryPrimeLifespanChoice n,
            markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n)
              (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
              (markedMemoryLineBirthAtom q n p.1) c := by
    have he := markedMemoryProjectiveFactor_lifespan_sum p.1 q (fun v => (d.position v).1)
      (fun v => hZ _ (d.position v).2) (markedMemoryPathVisits d j p) (hb j p)
    change _ / _ = ∑ c : MarkedMemoryPrimeLifespanChoice n,
      markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n) (markedMemoryPathPrimeLines hZ d p)
        (markedMemoryPathVisits d j p) (markedMemoryLineBirthAtom q n p.1) c at he
    exact (div_eq_iff (hb j p)).mp he |>.trans (mul_comm _ _)
  simp_rw [hp,Finset.prod_mul_distrib]
  congr 1
  unfold markedMemoryPathPrimeChoiceWeight
  symm
  calc
    _ = ∏ j,∑ cj : P j → MarkedMemoryPrimeLifespanChoice n,
        ∏ p : P j,markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n)
          (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
          (markedMemoryLineBirthAtom q n p.1) (cj p) :=
      (Fintype.prod_sum (fun j (cj : P j → MarkedMemoryPrimeLifespanChoice n) =>
        ∏ p : P j,markedMemoryPrimeLifespanChoiceWeight (markedMemoryEta q n)
          (markedMemoryPathPrimeLines hZ d p) (markedMemoryPathVisits d j p)
          (markedMemoryLineBirthAtom q n p.1) (cj p))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact (Fintype.prod_sum _).symm

end
end ArtinMatthews
