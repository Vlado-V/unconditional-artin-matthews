module

public import ArtinMatthews.GiantCandidateModelOneEachMass
public import ArtinMatthews.GiantCandidateModelOneEachWeights


set_option backward.privateInPublic true
@[expose] public section

/-! Summing the disjoint unique-pair events gives a genuine lower
bound on the one-hit-each mass in the independent model. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

def giantCandidateModelOneEachUnion {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) : Finset (GiantCandidateModelResidueSpace G j) := by
  classical
  exact (giantCandidateModelOneEachPairs G).biUnion
    (fun p => giantCandidateModelOneEachEvent G hG j p.1 p.2)

theorem giantCandidateModelOneEachUnion_card {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) :
    (giantCandidateModelOneEachUnion G hG j).card =
      ∑ p∈giantCandidateModelOneEachPairs G,(giantCandidateModelOneEachEvent G hG j p.1 p.2).card := by
  classical
  exact card_biUnion (giantCandidateModelOneEachPairs_disjoint G hG j)

theorem giantCandidateModelOneEachUnion_subset {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (j : ℕ) :
    giantCandidateModelOneEachUnion G hG j ⊆ giantCandidateModelResidueTuples G hG j :=
  fun t _ => giantCandidateModelResidueTuples_mem G hG j t

theorem giantCandidateModelOneEach_full_hitSet {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) (side : ι → GiantCandidateHitSide)
    (i : ι) (hfull : G i=giantCandidateSelectionPrimes G)
    {j : ℕ} {a b : giantCandidateSelectionPrimes G} (hab : a≠b)
    {t : GiantCandidateModelResidueSpace G j} (ht : t∈giantCandidateModelOneEachEvent G hG j a b) :
    let c := if side i=.predecessor then a else b
    giantCandidateModelHitSet G side t i = {c.val} := by
  let c := if side i=.predecessor then a else b
  have hiff (p : giantCandidateSelectionPrimes G) : giantCandidatePrimeResidueHit (side i) (t p) ↔ p=c := by
    have h := giantCandidateModelOneEach_residue_iff G hG hab ht p
    cases hs : side i
    · simpa [c,hs] using h.1
    · simpa [c,hs] using h.2
  change giantCandidateModelHitSet G side t i = {c.val}
  ext p
  by_cases hp : p∈giantCandidateSelectionPrimes G
  · let p₀ : giantCandidateSelectionPrimes G := ⟨p,hp⟩
    change p₀.val∈giantCandidateModelHitSet G side t i ↔ p₀.val∈({c.val}:Finset ℕ)
    rw [mem_giantCandidateModelHitSet,mem_singleton,hiff]
    exact ⟨fun h => congrArg Subtype.val h.2,
      fun h => ⟨hfull.symm ▸ hp,Subtype.ext h⟩⟩
  · have hnot : p∉giantCandidateModelHitSet G side t i := fun h =>
      hp (hfull ▸ (giantCandidateModelHitSet_subset G side t i h))
    exact iff_of_false hnot (fun h => hp ((mem_singleton.mp h).symm ▸ c.property))

theorem giantCandidateModelOneEachUnion_mass_ge {ι : Type*} [Fintype ι] (G : ι → Finset ℕ)
    (hG : ∀ i p,p∈G i → p.Prime) {j : ℕ} (hj : 0<j)
    (hlarge : ∀ p : giantCandidateSelectionPrimes G,4*(j:ℝ)≤(p.val:ℝ))
    (hsmall : ∀ p : giantCandidateSelectionPrimes G,(j:ℝ)/(p.val:ℝ)≤
      (∑ a : giantCandidateSelectionPrimes G,1/(a.val:ℝ))/2)
    (hmass : (∑ p : giantCandidateSelectionPrimes G,1/(p.val:ℝ))≤1) :
    let V := ∑ p : giantCandidateSelectionPrimes G,1/(p.val:ℝ)
    Real.exp (-(4*(j:ℝ)))*(V^2/4)≤
      ((giantCandidateModelOneEachUnion G hG j).card:ℝ)/((giantCandidateModelResidueTuples G hG j).card:ℝ) := by
  let U := giantCandidateSelectionPrimes G
  let V := ∑ p : U,1/(p.val:ℝ)
  let R := Real.exp (-(4*(j:ℝ)))
  let S := giantCandidateModelOneEachPairs G
  let w (p : U × U) := giantCandidateModelHitAtom G hG j p.1 .predecessor*
    giantCandidateModelHitAtom G hG j p.2 .product
  let T := giantCandidateModelResidueTuples G hG j
  let M := giantCandidateModelOneEachUnion G hG j
  have hweight : V^2/4≤∑ p∈S,w p :=
    giantCandidateModelOneEach_weights_ge G hG hj
      (fun p => by linarith only [hlarge p,Nat.cast_nonneg (α:=ℝ) j]) hsmall
  have hn : R≤∏ p : U,giantCandidateModelNoHitAtom G hG j p :=
    giantCandidateModelNoHitProduct_ge G hG hj hlarge hmass
  change R*(V^2/4)≤(M.card:ℝ)/(T.card:ℝ)
  calc
    _ ≤ R*(∑ p∈S,w p) := mul_le_mul_of_nonneg_left hweight (Real.exp_nonneg _)
    _ = ∑ p∈S,w p*R := by rw [mul_comm,sum_mul]
    _ ≤ ∑ p∈S,((giantCandidateModelOneEachEvent G hG j p.1 p.2).card:ℝ)/(T.card:ℝ) := by
      apply sum_le_sum
      intro p hp
      have hpair : p.1≠p.2 := (mem_filter.mp hp).2
      have hw : 0≤w p := mul_nonneg (giantCandidateModelHitAtom_nonneg G hG j p.1 _)
        (giantCandidateModelHitAtom_nonneg G hG j p.2 _)
      exact (mul_le_mul_of_nonneg_left hn hw).trans
        (giantCandidateModelOneEach_mass_ge_full_noHit G hG j p.1 p.2 hpair)
    _ = _ := by
      rw [← sum_div,← Nat.cast_sum,← giantCandidateModelOneEachUnion_card G hG j]

end
end ArtinMatthews
