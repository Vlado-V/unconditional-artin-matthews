module

public import ArtinMatthews.GiantCandidateAllocationEquiv


set_option backward.privateInPublic true
@[expose] public section

/-! Exact allocation of active prime factors in the literal stripped
proxy. The fixed character remains evaluated at the original integer.
Only the stripped tuple contributes to the invariant core. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

private theorem giantCandidateStrippedSlotCoefficient_mul_prime_product (C P : Finset ℕ)
    (hPC : P ⊆ C) (hP : ∀ p ∈ P, p.Prime) {W z : ℝ} (hW : 0 ≤ W)
    (hPW : ∀ p ∈ P, W < (p : ℝ)) (S : Finset ℕ) (hS : S ⊆ P)
    {m : ℕ} (hm : 0 < m) :
    giantCandidateStrippedSlotCoefficient C W z ((∏ p ∈ S, p) * m) =
      giantCandidateStrippedSlotCoefficient C W z m := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have hp := hS (mem_insert_self p S)
    have hsub : S ⊆ P := fun q hq => hS (mem_insert_of_mem hq)
    have hprod : 0 < ∏ q ∈ S, q := prod_pos (fun q hq => (hP q (hsub hq)).pos)
    rw [prod_insert hpS, mul_assoc,
      giantCandidateStrippedSlotCoefficient_mul_prime C hW (hP p hp) (hPC hp) (hPW p hp)
        (Nat.mul_pos hprod hm), ih hsub]

theorem giantCandidateStrippedSlotCoefficient_mul_active_part (C P : Finset ℕ)
    (hPC : P ⊆ C) (hP : ∀ p ∈ P, p.Prime) {W z : ℝ} (hW : 0 ≤ W)
    (hPW : ∀ p ∈ P, W < (p : ℝ)) {n a m : ℕ} (hn : 0 < n)
    (hnsq : ∀ p ∈ P, ¬ p ^ 2 ∣ n) (ha : a ∣ giantCandidatePrimePart P n) (hm : 0 < m) :
    giantCandidateStrippedSlotCoefficient C W z (m * a) =
      giantCandidateStrippedSlotCoefficient C W z m := by
  have hsq := (giantCandidatePrimePart_squarefree P hP hn hnsq).squarefree_of_dvd ha
  have hsub : a.primeFactors ⊆ P := by
    intro p hp
    have h := Nat.primeFactors_mono ha (commonPrimePart_ne_zero hn.ne' _) hp
    rw [giantCandidatePrimePart_primeFactors P hP hn] at h
    exact (mem_filter.mp h).1
  rw [mul_comm m a, ← Nat.prod_primeFactors_of_squarefree hsq]
  exact giantCandidateStrippedSlotCoefficient_mul_prime_product C P hPC hP hW hPW
    a.primeFactors hsub hm

/-- The core of the literal allocation in Section 7. All candidate
prime parts are removed in the slot coefficient, while only the active
part is removed from the product of the stripped tuple. -/
def giantCandidateAllocationCore (C P : Finset ℕ) (W z : ℝ) (j n : ℕ) : ℂ :=
  ∑ e ∈ giantOrderedProductFiber j (giantCandidateStrip P n),
    ∏ i, giantCandidateStrippedSlotCoefficient C W z (e i)

theorem giantCandidateAllocationCore_strip (C P : Finset ℕ) (W z : ℝ) (j n : ℕ) :
    giantCandidateAllocationCore C P W z j (giantCandidateStrip P n) =
      giantCandidateAllocationCore C P W z j n := by
  simp only [giantCandidateAllocationCore, giantCandidateStrip_idem]

theorem giantCandidateAllocationFiber_sum (C P : Finset ℕ) (hPC : P ⊆ C)
    (hP : ∀ p ∈ P, p.Prime) {W z : ℝ} (hW : 0 ≤ W)
    (hPW : ∀ p ∈ P, W < (p : ℝ)) {M : ℕ} (χ : DirichletCharacter ℂ M)
    (j : ℕ) {n : ℕ} (hn : 0 < n) (hnsq : ∀ p ∈ P, ¬ p ^ 2 ∣ n) :
    (∑ t ∈ giantOrderedProductFiber j n,
      ∏ i, χ (t i) * giantCandidateStrippedSlotCoefficient C W z (t i)) =
      χ n * (j : ℂ) ^ bandCount P n * giantCandidateAllocationCore C P W z j n := by
  classical
  let F := giantOrderedProductFiber j n
  let E := giantOrderedProductFiber j (giantCandidateStrip P n)
  let A := giantOrderedProductFiber j (giantCandidatePrimePart P n)
  let coef := giantCandidateStrippedSlotCoefficient C W z
  let g (t : Fin j → ℕ) : ℂ := ∏ i, coef (t i)
  have hχ : (∑ t ∈ F, ∏ i, χ (t i) * coef (t i)) = χ n * ∑ t ∈ F, g t := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro t ht
    have htprod := (mem_giantOrderedProductFiber.mp ht).2
    simp only [prod_mul_distrib, ← map_prod, ← Nat.cast_prod, htprod, g]
  have hsplit : (∑ t ∈ F, g t) =
      ∑ s : ↥E × ↥A, g (fun i => s.1.val i * s.2.val i) := by
    calc
      _ = ∑ t : ↥F, g t.val := (sum_coe_sort F g).symm
      _ = _ := (Equiv.sum_comp (giantCandidateAllocationEquiv P j n hn).symm
        (fun t : ↥F => g t.val)).symm
  have hind : (∑ s : ↥E × ↥A, g (fun i => s.1.val i * s.2.val i)) =
      ∑ s : ↥E × ↥A, g s.1.val := by
    apply sum_congr rfl
    intro s _
    unfold g
    apply prod_congr rfl
    intro i _
    exact giantCandidateStrippedSlotCoefficient_mul_active_part C P hPC hP hW hPW hn hnsq
      (Nat.dvd_of_mem_finMulAntidiag s.2.property i)
      ((mem_giantOrderedProductFiber.mp s.1.property).1 i)
  have hcount : (∑ s : ↥E × ↥A, g s.1.val) =
      (j : ℂ) ^ bandCount P n * giantCandidateAllocationCore C P W z j n := by
    have hcard : Fintype.card ↥A = j ^ bandCount P n := by
      rw [Fintype.card_coe]
      exact giantCandidatePrimePart_fiber_card P hP j hn hnsq
    rw [Fintype.sum_prod_type]
    simp only [sum_const, card_univ, nsmul_eq_mul, hcard, Nat.cast_pow, ← Finset.mul_sum,
      Finset.sum_coe_sort]
    rfl
  change (∑ t ∈ F, ∏ i, χ (t i) * coef (t i)) = _
  rw [hχ, hsplit, hind, hcount]
  ring

end
end ArtinMatthews
