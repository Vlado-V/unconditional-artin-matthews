module

public import ArtinMatthews.GiantCandidateCoinProxy


set_option backward.privateInPublic true
@[expose] public section

/-! Only the retained proxy is expanded. Each signed term is the literal
unguarded marked proxy on the union of the success and chosen failure sets. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

theorem giantCandidateRetainedStrippedProxy_eq_expansion {J : Type*} [Fintype J]
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M) (ε : ℝ) (Φ : ℝ → ℝ)
    (T γ : ℝ) (j : ℕ) (x threshold c q : ℝ) :
    giantCandidateWeightedStrippedProxy e χ ε Φ T γ j x
      (giantCandidateRetainedCoinMass x threshold c q j) =
      ∑ p ∈ giantCandidateCoinTerms x threshold,
        giantCandidateCoinTermCoefficient x c p *
          giantCandidateActualUnguardedMarkedProxyTerm (giantCandidateFullPrimes x)
            (fun i : ↥(p.1 ∪ p.2) => giantCandidateGroup x i.val) e χ ε Φ T γ q j x := by
  let S := giantOrderedProductTuples j ⌊T*x⌋₊
  let E := giantCandidateCoinTerms x threshold
  let A (p : GiantCandidateCoinTerm x) := giantCandidateCoinTermCoefficient x c p
  let v (t : Fin j → ℕ) := ∏ i,t i
  let P (p : GiantCandidateCoinTerm x) (i : ↥(p.1 ∪ p.2)) := giantCandidateGroup x i.val
  let L (p : GiantCandidateCoinTerm x) (n : ℕ) : ℂ := giantCandidateActiveOneMark (P p) q (n-1)
  let R (p : GiantCandidateCoinTerm x) (n : ℕ) : ℂ := giantCandidateActiveOneMark (P p) (q/(j:ℝ)) n
  let W (n : ℕ) := markedExtractionWeight e (giantMarkedCenteredCore ε) Φ x n
  let a := giantCandidateStrippedSlotCoefficient (giantCandidateFullPrimes x)
    (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)
  let B (t : Fin j → ℕ) := ∏ i,χ (t i)*a (t i)
  let F (p : GiantCandidateCoinTerm x) (t : Fin j → ℕ) :=
    W (v t)*L p (v t)*(B t*R p (v t))
  have hsum :
      (∑ t ∈ S,W (v t)*B t*(giantCandidateRetainedCoinMass x threshold c q j (v t):ℂ)) =
        ∑ p ∈ E,A p*∑ t ∈ S,F p t := by
    calc
      _ = ∑ t ∈ S,∑ p ∈ E,A p*F p t := by
        apply sum_congr rfl
        intro t _
        rw [giantCandidateRetainedCoinMass_eq_signed]
        change W (v t)*B t*(∑ p ∈ E,A p*L p (v t)*R p (v t)) = _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro p _
        dsimp only [F]
        ring
      _ = _ := by rw [sum_comm]; simp only [Finset.mul_sum]
  change (∑ t ∈ S,W (v t)*B t*(giantCandidateRetainedCoinMass x threshold c q j (v t):ℂ)) /
      (j.factorial:ℂ) = ∑ p ∈ E,A p*((∑ t ∈ S,F p t)/(j.factorial:ℂ))
  rw [hsum]
  simp only [div_eq_mul_inv,Finset.sum_mul,mul_assoc]

def giantCandidateSignedCorrelationSum {J : Type*} [Fintype J]
    (e : J → ℝ) {M : ℕ} (χ : DirichletCharacter ℂ M) (ε : ℝ) (Φ : ℝ → ℝ)
    (T γ : ℝ) (j : ℕ) (x threshold c q : ℝ) : ℂ :=
  ∑ p ∈ giantCandidateCoinTerms x threshold,
    giantCandidateCoinTermCoefficient x c p * (((j:ℂ)^(p.1 ∪ p.2).card/j.factorial) *
      ((x:ℂ)*giantCandidateActualUnguardedShiftedCorrelation (giantCandidateFullPrimes x)
        (fun i : ↥(p.1 ∪ p.2) => giantCandidateGroup x i.val) e χ ε Φ T γ q j x))

end
end ArtinMatthews
