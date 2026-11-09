module

public import ArtinMatthews.GiantTwoSidedResidueRootSum
public import ArtinMatthews.GiantTwoSidedResiduePrimeFactor
public import ArtinMatthews.GiantTwoSidedActiveModulus


set_option backward.privateInPublic true
@[expose] public section

/-! The full Haar expectation equals the fixed-label product density,
including the deterministic used-prime factor and the active modulus. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem giantTwoSidedIndependentResidueMean_nonneg {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    {q : ℝ} (hq : 0 ≤ q) (offset : Fin (n+1) → ℤ) :
    0 ≤ giantTwoSidedIndependentResidueMean labels q offset :=
  div_nonneg (sum_nonneg fun root _ =>
    giantTwoSidedIndependentResidueFactor_nonneg P labels hq offset root) (Nat.cast_nonneg _)

theorem giantTwoSidedIndependentResidueFactor_incompatible {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M n : ℕ} (labels : Fin (n+1) → MarkedPhysicalMarking P M)
    (q : ℝ) (offset : Fin (n+1) → ℤ)
    (hc : ¬GiantTwoSidedActiveCompatible univ labels offset) (root : GiantTwoSidedFullResidue P) :
    giantTwoSidedIndependentResidueFactor P labels q offset root=0 := by
  apply giantTwoSidedIndependentResidueFactor_zero
  intro h
  apply hc
  have hz (v : Fin (n+1)) (p : ℕ) (hp : p∈markedPhysicalActivePrimes (labels v)) :
      p∈giantTwoSidedResidueZeros (giantTwoSidedResidueTranslate (offset v) root) := by
    obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
    obtain ⟨l,_,rfl⟩ := mem_image.mp hj
    exact (mem_giantTwoSidedResidueZeros _ _).mpr (h v j l)
  intro p v _ hp
  let p' : ↥(markedPhysicalBandPrimes P) :=
    ⟨p.val,markedPhysicalPathUsedPrimes_subset univ labels p.property⟩
  have hv : root p'+(offset v:ZMod p.val)=0 :=
    (mem_giantTwoSidedResidueZeros _ p').mp (hz v p.val hp)
  have hb : root p'+(offset (giantTwoSidedActiveVisit univ labels p).val:ZMod p.val)=0 :=
    (mem_giantTwoSidedResidueZeros _ p').mp
      (hz _ p.val (giantTwoSidedActiveVisit_mem univ labels p))
  linear_combination hv-hb

theorem giantTwoSidedIndependentResidueMean_density {J : Type*} [Fintype J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) {M n : ℕ}
    (labels : Fin (n+1) → MarkedPhysicalMarking P M) (q : ℝ) (offset : Fin (n+1) → ℤ) :
    giantTwoSidedIndependentResidueMean labels q offset=
      if GiantTwoSidedActiveCompatible univ labels offset then
        giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset /
          giantTwoSidedActiveModulus labels *
          ∏ p∈markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels,
            (1-scalarWeightedResidueMean (giantTwoSidedResidueLossNat univ
              (markedMemoryVisitQ q n) offset) p)
      else 0 := by
  by_cases hc : GiantTwoSidedActiveCompatible univ labels offset
  · rw [ite_eq_left hc]
    unfold giantTwoSidedIndependentResidueMean
    rw [giantTwoSidedIndependentResidue_mean_product hdis]
    let μ := giantTwoSidedIndependentPrimeMean labels (markedMemoryVisitQ q n) offset
    have hprime (p : ℕ) (hp : p∈markedPhysicalBandPrimes P) : p.Prime := by
      obtain ⟨j,_,hj⟩ := mem_biUnion.mp hp
      exact hP j p hj
    have hused : (∏ p∈markedPhysicalPathUsedPrimes univ labels,μ p)=
        giantTwoSidedActiveResidueWeight univ labels (markedMemoryVisitQ q n) offset /
          giantTwoSidedActiveModulus labels := by
      rw [← prod_coe_sort (markedPhysicalPathUsedPrimes univ labels)]
      have he (p : ↥(markedPhysicalPathUsedPrimes univ labels)) : μ p.val=
          (∏ v : Fin (n+1),if p.val∈markedPhysicalActivePrimes (labels v) then 1 else
            if (offset v:ZMod p.val)=(offset (giantTwoSidedActiveVisit univ labels p).val:ZMod p.val)
              then markedMemoryVisitQ q n v else 1)/p.val := by
        let : NeZero p.val := ⟨(hprime p.val (markedPhysicalPathUsedPrimes_subset univ labels p.property)).ne_zero⟩
        exact giantTwoSidedIndependentPrimeMean_used labels _ offset hc p
      simp_rw [he]
      rw [prod_div_distrib]
      unfold giantTwoSidedActiveResidueWeight giantTwoSidedActiveModulus
      congr 1
      rw [← Nat.cast_prod]
      exact congrArg (fun a : ℕ => (a:ℝ))
        (prod_coe_sort (markedPhysicalPathUsedPrimes univ labels) (fun p : ℕ => p))
    have hunused : (∏ p∈markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels,μ p)=
        ∏ p∈markedPhysicalBandPrimes P \ markedPhysicalPathUsedPrimes univ labels,
          (1-scalarWeightedResidueMean (giantTwoSidedResidueLossNat univ
            (markedMemoryVisitQ q n) offset) p) := by
      apply prod_congr rfl
      intro p hp
      let : NeZero p := ⟨(hprime p (mem_sdiff.mp hp).1).ne_zero⟩
      exact giantTwoSidedIndependentPrimeMean_unused labels _ offset p (mem_sdiff.mp hp).2
    have hs := prod_sdiff (f:=μ) (markedPhysicalPathUsedPrimes_subset univ labels)
    rw [mul_comm] at hs
    change (∏ p∈markedPhysicalBandPrimes P,μ p)=_
    rw [← hs,hused,hunused]
  · rw [ite_eq_right hc]
    unfold giantTwoSidedIndependentResidueMean
    simp only [giantTwoSidedIndependentResidueFactor_incompatible labels q offset hc,sum_const_zero,zero_div]

end
end ArtinMatthews
