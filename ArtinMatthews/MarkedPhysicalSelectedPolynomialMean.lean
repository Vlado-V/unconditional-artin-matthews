module

public import ArtinMatthews.MarkedPhysicalBandLineValidity
public import ArtinMatthews.MarkedPhysicalBandLineBonferroni


set_option backward.privateInPublic true
@[expose] public section

/-! Summing the actual selected-modulus means gives the full-band
Bonferroni polynomial. Each modulus keeps its own matrix-class average;
ordered-label distinctness remains a literal guard. -/
namespace ArtinMatthews
open scoped BigOperators Classical
noncomputable section

def markedPhysicalSelectedGuardedPolynomialMean {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p ∈ P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1),(-1:ℝ)^j *
    ∑ T ∈ (markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes Finset.univ a).powersetCard j,
      if hT : T ⊆ markedPhysicalBandPrimes P then
        markedPhysicalSelectedGuardedMonomialMean hP a (markedMemoryVisitQ q N) z hz T hT else 0

theorem markedPhysicalSelectedGuardedPolynomialMean_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M N : ℕ} (hP : ∀ j p,p ∈ P j → p.Prime)
    (a : Fin (N+1) → MarkedPhysicalMarking P M) (q : ℝ)
    (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2) (k : ℕ) :
    markedPhysicalSelectedGuardedPolynomialMean hP a q z hz k =
      if ∀ v,MarkedPhysicalMarkingDistinct (a v) then
        markedPhysicalIndependentBonferroni hP a q z hz k else 0 := by
  let E := markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes Finset.univ a
  let D : ℝ := Fintype.card (MarkedPhysicalBandLines P)
  let G := fun ell : MarkedPhysicalBandLines P =>
    (∀ v,MarkedPhysicalMarkingDistinct (a v)) ∧ MarkedPhysicalBandLineGuard hP a z hz ell
  have hmean (j : ℕ) (T : Finset ℕ) (hT : T ∈ E.powersetCard j) :
      (if ht : T ⊆ markedPhysicalBandPrimes P then
        markedPhysicalSelectedGuardedMonomialMean hP a (markedMemoryVisitQ q N) z hz T ht else 0) =
      (∑ ell : MarkedPhysicalBandLines P,if G ell then
        markedPhysicalBandLineMonomial hP ell Finset.univ a (markedMemoryVisitQ q N) z hz T else 0)/D := by
    have ht : T ⊆ markedPhysicalBandPrimes P :=
      fun p hp => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1
    rw [dite_eq_left ht,markedPhysicalSelectedGuardedMonomialMean_common_lines]
  have hs : markedPhysicalSelectedGuardedPolynomialMean hP a q z hz k =
      (∑ ell : MarkedPhysicalBandLines P,if G ell then
        markedPhysicalBandLinePolynomial hP ell Finset.univ a (markedMemoryVisitQ q N) z hz k else 0)/D := by
    unfold markedPhysicalSelectedGuardedPolynomialMean
    change (∑ j ∈ Finset.range (k+1),(-1:ℝ)^j * ∑ T ∈ E.powersetCard j, _) = _
    simp_rw [Finset.sum_congr rfl (fun T hT => hmean _ T hT)]
    calc
      _ = (∑ j ∈ Finset.range (k+1),∑ T ∈ E.powersetCard j,
          ∑ ell : MarkedPhysicalBandLines P,(-1:ℝ)^j *
            (if G ell then markedPhysicalBandLineMonomial hP ell Finset.univ a
              (markedMemoryVisitQ q N) z hz T else 0))/D := by
        simp only [Finset.sum_div,Finset.mul_sum,mul_div_assoc]
      _ = (∑ ell : MarkedPhysicalBandLines P,∑ j ∈ Finset.range (k+1),
          ∑ T ∈ E.powersetCard j,(-1:ℝ)^j *
            (if G ell then markedPhysicalBandLineMonomial hP ell Finset.univ a
              (markedMemoryVisitQ q N) z hz T else 0))/D := by
        congr 1
        simp_rw [Finset.sum_comm (s := E.powersetCard _)]
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro ell _
        by_cases hg : G ell
        · simp only [hg,ite_true]
          rw [markedPhysicalBandLinePolynomial_monomials]
          simp only [Finset.mul_sum,E]
        · simp only [hg,ite_false,mul_zero,Finset.sum_const_zero]
  rw [hs]
  by_cases ha : ∀ v,MarkedPhysicalMarkingDistinct (a v)
  · simp [G,ha,markedPhysicalIndependentBonferroni,D]
  · simp [G,ha]

end
end ArtinMatthews
