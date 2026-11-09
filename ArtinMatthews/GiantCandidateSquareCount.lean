module

public import ArtinMatthews.GiantCandidateGroups
public import ArtinMatthews.MarkedTypeIICollisionDecay
public import Mathlib.Data.Nat.Factorization.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The exact product-level candidate-square exceptions. Counting actual
multiples gives a bound by the sum of reciprocal prime squares. -/
namespace ArtinMatthews
open Finset Filter
open scoped BigOperators
noncomputable section

def giantCandidateSquareExceptions (C : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (range (X+1)).filter fun n => n ≠ 0 ∧ ∃ p ∈ C, p^2 ∣ n

theorem mem_giantCandidateSquareExceptions {C : Finset ℕ} {X n : ℕ} :
    n ∈ giantCandidateSquareExceptions C X ↔ 0 < n ∧ n ≤ X ∧ ∃ p ∈ C, p^2 ∣ n := by
  simp only [giantCandidateSquareExceptions, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.pos_iff_ne_zero]
  tauto

theorem giantCandidateSquareExceptions_card_le_multiples (C : Finset ℕ) (X : ℕ) :
    (giantCandidateSquareExceptions C X).card ≤ ∑ p ∈ C, X / p^2 := by
  let Q (p : ℕ) := (range (X+1)).filter fun n => n ≠ 0 ∧ p^2 ∣ n
  have hsub : giantCandidateSquareExceptions C X ⊆ C.biUnion Q := by
    intro n hn
    obtain ⟨hn0,hnX,p,hp,hpn⟩ := mem_giantCandidateSquareExceptions.mp hn
    exact mem_biUnion.mpr ⟨p,hp,mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hnX),hn0.ne',hpn⟩⟩
  calc
    _ ≤ (C.biUnion Q).card := card_le_card hsub
    _ ≤ ∑ p ∈ C, (Q p).card := card_biUnion_le
    _ = _ := sum_congr rfl (fun p _ => Nat.card_multiples' X (p^2))

theorem giantCandidateSquareExceptions_card_le (C : Finset ℕ) (X : ℕ) :
    ((giantCandidateSquareExceptions C X).card:ℝ) ≤
      (X:ℝ)*∑ p ∈ C, 1/(p:ℝ)^2 := by
  calc
    _ ≤ ∑ p ∈ C, ((X/p^2:ℕ):ℝ) := by exact_mod_cast giantCandidateSquareExceptions_card_le_multiples C X
    _ ≤ ∑ p ∈ C, (X:ℝ)/(p:ℝ)^2 := by
      apply sum_le_sum
      intro p _
      exact_mod_cast (Nat.cast_div_le (m:=X) (n:=p^2) (α:=ℝ))
    _ = _ := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro p _
      ring

theorem giantCandidateSquareExceptions_actual_card_eventually :
    ∀ᶠ x : ℝ in atTop, ∀ X : ℕ,
      ((giantCandidateSquareExceptions (giantCandidateFullPrimes x) X).card:ℝ) ≤
        4*(X:ℝ)*Real.exp (-(Real.log x)^(28/100:ℝ)) := by
  have ht := Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<28/100)).comp Real.tendsto_log_atTop)
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    ht.eventually (eventually_ge_atTop (4:ℝ))] with x hx hlog h4
  intro X
  have hp : ∀ p ∈ giantCandidateFullPrimes x, Real.exp ((Real.log x)^(28/100:ℝ)) ≤ (p:ℝ) :=
    fun p hp => (giantCandidateFullPrimes_range hx hlog hp).2.1
  calc
    _ ≤ (X:ℝ)*(4/Real.exp ((Real.log x)^(28/100:ℝ))) :=
      (giantCandidateSquareExceptions_card_le _ _).trans
        (mul_le_mul_of_nonneg_left (marked_reciprocal_square_tail_le _ h4 hp) (Nat.cast_nonneg X))
    _ = _ := by rw [Real.exp_neg]; ring

end
end ArtinMatthews
