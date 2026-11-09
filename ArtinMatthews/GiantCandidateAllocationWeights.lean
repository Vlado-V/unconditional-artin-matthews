module

public import ArtinMatthews.GiantCandidateAllocationCore


set_option backward.privateInPublic true
@[expose] public section

/-! Exact one-mark damping under allocation. The active groups keep their
actual reciprocal masses, and groups with no hits retain zero weight. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

def giantCandidateActiveOneMark {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (q : ℝ) (n : ℕ) : ℝ :=
  ∏ i, ((bandCount (P i) n : ℝ) / bandReciprocalMass (P i)) * q ^ (bandCount (P i) n - 1)

theorem giantCandidateActiveOneMark_half {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (n : ℕ) :
    giantCandidateActiveOneMark P (1/2) n =
      divisorWeight univ P (fun i => bandReciprocalMass (P i)) n := by
  unfold giantCandidateActiveOneMark divisorWeight
  apply prod_congr rfl
  intro i _
  unfold bandWeight halfDampedCount
  ring

theorem giantCandidateBandCount_union {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (n : ℕ) :
    bandCount (univ.biUnion P) n = ∑ i, bandCount (P i) n := by
  classical
  have hE : activeDivisors (univ.biUnion P) n =
      univ.biUnion (fun i => activeDivisors (P i) n) := by
    ext p
    simp only [activeDivisors, mem_filter, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, hi⟩, hd⟩
      exact ⟨i, hi, hd⟩
    · rintro ⟨i, hi, hd⟩
      exact ⟨⟨i, hi⟩, hd⟩
  unfold bandCount
  rw [hE, card_biUnion]
  intro i _ j _ hij
  exact (hdis hij).mono (filter_subset _ _) (filter_subset _ _)

private theorem giantCandidateOneMark_alloc_factor (j ω : ℕ) (hj : 0 < j) (V q : ℝ) :
    (j : ℝ) ^ ω * ((ω : ℝ) / V * (q / (j : ℝ)) ^ (ω - 1)) =
      (j : ℝ) * ((ω : ℝ) / V * q ^ (ω - 1)) := by
  cases ω with
  | zero => simp
  | succ k =>
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    have hq : (j : ℝ) * (q / (j : ℝ)) = q := by field_simp
    rw [Nat.succ_sub_one, pow_succ]
    calc
      _ = ((j : ℝ) ^ k * (q / (j : ℝ)) ^ k) * ((k.succ : ℝ) / V) * (j : ℝ) := by ring
      _ = _ := by rw [← mul_pow, hq]; ring

theorem giantCandidateActiveOneMark_allocation {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (j n : ℕ) (hj : 0 < j) (q : ℝ) :
    (j : ℝ) ^ bandCount (univ.biUnion P) n * giantCandidateActiveOneMark P (q / (j : ℝ)) n =
      (j : ℝ) ^ Fintype.card ι * giantCandidateActiveOneMark P q n := by
  rw [giantCandidateBandCount_union P hdis n, ← prod_pow_eq_pow_sum]
  unfold giantCandidateActiveOneMark
  rw [← prod_mul_distrib]
  calc
    _ = ∏ i, (j : ℝ) * (((bandCount (P i) n : ℝ) / bandReciprocalMass (P i)) *
        q ^ (bandCount (P i) n - 1)) := by
      apply prod_congr rfl
      intro i _
      exact giantCandidateOneMark_alloc_factor j (bandCount (P i) n) hj _ q
    _ = _ := by rw [prod_mul_distrib, prod_const, card_univ]

theorem giantCandidateAllocation_marked_fiber_sum {ι : Type*} [Fintype ι]
    (C : Finset ℕ) (P : ι → Finset ℕ) (hPC : univ.biUnion P ⊆ C)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    {W z : ℝ} (hW : 0 ≤ W) (hPW : ∀ p ∈ univ.biUnion P, W < (p : ℝ))
    {M : ℕ} (χ : DirichletCharacter ℂ M) (j : ℕ) (hj : 0 < j) {n : ℕ}
    (hn : 0 < n) (hnsq : ∀ p ∈ univ.biUnion P, ¬ p ^ 2 ∣ n) (q : ℝ) :
    (∑ t ∈ giantOrderedProductFiber j n,
      (∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C W z (t i)) *
        (giantCandidateActiveOneMark P (q / (j : ℝ)) n : ℂ)) =
      χ n * (j : ℂ) ^ Fintype.card ι * (giantCandidateActiveOneMark P q n : ℂ) *
        giantCandidateAllocationCore C (univ.biUnion P) W z j n := by
  rw [← sum_mul, giantCandidateAllocationFiber_sum C (univ.biUnion P) hPC hP hW hPW χ j hn hnsq]
  have h := congrArg (fun r : ℝ => (r : ℂ)) (giantCandidateActiveOneMark_allocation P hdis j n hj q)
  push_cast at h
  calc
    _ = χ n * ((j : ℂ) ^ bandCount (univ.biUnion P) n *
        (giantCandidateActiveOneMark P (q / (j : ℝ)) n : ℂ)) *
          giantCandidateAllocationCore C (univ.biUnion P) W z j n := by ring
    _ = _ := by rw [h]; ring

end
end ArtinMatthews
