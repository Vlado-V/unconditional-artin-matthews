module

public import ArtinMatthews.GiantCandidateAllocationGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The literal stripped core is dominated by the original product fiber.
Multiplying one slot by the removed part gives the required injection. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

theorem giantOrderedProductFiber_card_le_of_dvd (j : ℕ) (hj : 0 < j)
    {m n : ℕ} (hn : 0 < n) (hmn : m ∣ n) :
    (giantOrderedProductFiber j m).card ≤ (giantOrderedProductFiber j n).card := by
  obtain ⟨d,rfl⟩ := hmn
  have hd : 0 < d := Nat.pos_of_ne_zero (Nat.mul_ne_zero_iff.mp hn.ne').2
  cases j with
  | zero => omega
  | succ k =>
    let f (t : Fin (k+1) → ℕ) := Fin.cons (t 0*d) (Fin.tail t)
    apply card_le_card_of_injOn f
    · intro t ht
      obtain ⟨hpos,hprod⟩ := mem_giantOrderedProductFiber.mp ht
      apply mem_giantOrderedProductFiber.mpr
      refine ⟨?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun a => ?_) i
        · simpa only [f,Fin.cons_zero] using Nat.mul_pos (hpos 0) hd
        · simpa only [f,Fin.cons_succ,Fin.tail] using hpos a.succ
      · rw [Fin.prod_univ_succ t] at hprod
        rw [Fin.prod_univ_succ]
        simp only [f,Fin.cons_zero,Fin.cons_succ,Fin.tail]
        calc
          _ = (t 0*∏ i : Fin k,t i.succ)*d := by ac_rfl
          _ = _ := by rw [hprod]
    · intro t _ u _ he
      funext i
      refine Fin.cases ?_ (fun a => ?_) i
      · have h := congrFun he 0
        exact Nat.eq_of_mul_eq_mul_right hd (by simpa only [f,Fin.cons_zero] using h)
      · simpa only [f,Fin.cons_succ,Fin.tail] using congrFun he a.succ

theorem giantCandidateStrippedSlotCoefficient_actual_norm_le_one (γ : ℝ) (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop,∀ (C : Finset ℕ) (m : ℕ),
      ‖giantCandidateStrippedSlotCoefficient C (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) m‖ ≤ 1 := by
  filter_upwards [giantCandidateSlotBound_actual_le_one γ hγ] with x hx
  intro C m
  apply (giantCandidateStrippedSlotCoefficient_norm_le_envelope C hx.1 m).trans
  unfold giantCandidateProxyEnvelope
  split_ifs
  · exact hx.2
  · exact zero_le_one

theorem giantCandidateAllocationCore_actual_norm_le_fiber (γ : ℝ) (hγ : 0 < γ)
    (j : ℕ) (hj : 0 < j) :
    ∀ᶠ x : ℝ in atTop,∀ (C P : Finset ℕ) (n : ℕ), 0 < n →
      ‖giantCandidateAllocationCore C P (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ) j n‖ ≤
        ((giantOrderedProductFiber j n).card:ℝ) := by
  filter_upwards [giantCandidateStrippedSlotCoefficient_actual_norm_le_one γ hγ] with x hx
  intro C P n hn
  let E := giantOrderedProductFiber j (giantCandidateStrip P n)
  let a := giantCandidateStrippedSlotCoefficient C (Real.exp ((Real.log x)^(6/25:ℝ))) (x^γ)
  change ‖∑ t ∈ E,∏ i,a (t i)‖ ≤ _
  calc
    _ ≤ ∑ t ∈ E,‖∏ i,a (t i)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ E,(1:ℝ) := by
      apply sum_le_sum
      intro t _
      rw [norm_prod]
      exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => hx C (t i))
    _ = (E.card:ℝ) := by simp only [sum_const,nsmul_eq_mul,mul_one]
    _ ≤ _ := by exact_mod_cast giantOrderedProductFiber_card_le_of_dvd j hj hn (giantCandidateStrip_dvd P n)

end
end ArtinMatthews
