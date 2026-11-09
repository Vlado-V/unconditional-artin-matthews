module

public import ArtinMatthews.GiantCandidateResidueFullDyad
public import ArtinMatthews.GiantCandidateGroups


set_option backward.privateInPublic true
@[expose] public section

/-! The modulus is the product of the selected actual candidate primes.
A fixed bound on their number is enough for uniform full-dyad counts. -/

namespace ArtinMatthews
noncomputable section
open Finset Filter
open scoped BigOperators

def giantCandidateResidueModulus (U : Finset ℕ) : ℕ :=
  ∏ p∈U,p

theorem giantCandidateActualResidueModulus_eventually (r : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U : Finset ℕ,U ⊆ giantCandidateFullPrimes x → U.card≤r →
      let Q := giantCandidateResidueModulus U
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      0<Q ∧ (Q:ℝ) ≤ Real.exp ((r:ℝ)*(Real.log x)^(9/20:ℝ)) ∧
        ∀ p∈Nat.primesLE ⌊W⌋₊,p.Coprime Q := by
  filter_upwards [giantCandidateFullPrimes_prime_upper_eventually,
    giantCandidateFullPrimes_gt_W_eventually,Real.tendsto_log_atTop.eventually_ge_atTop (0:ℝ)]
    with x hprime hbig hL
  intro U hU hr
  let Q := giantCandidateResidueModulus U
  let W := Real.exp ((Real.log x)^(6/25:ℝ))
  let A := (Real.log x)^(9/20:ℝ)
  have hA : 0 ≤ A := Real.rpow_nonneg hL _
  have hP (p : ℕ) (hp : p∈U) : p.Prime ∧ (p:ℝ) ≤ Real.exp A := by
    refine ⟨(hprime p (hU hp)).1,?_⟩
    change (p:ℝ) ≤ Real.exp ((Real.log x)^(9/20:ℝ))
    simpa only [show (45/100:ℝ)=9/20 by norm_num] using (hprime p (hU hp)).2
  change 0<Q ∧ (Q:ℝ)≤Real.exp ((r:ℝ)*A) ∧ ∀p∈Nat.primesLE ⌊W⌋₊,p.Coprime Q
  refine ⟨prod_pos (fun p hp => (hP p hp).1.pos),?_,?_⟩
  · change (((∏ p∈U,p):ℕ):ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _p∈U,Real.exp A := prod_le_prod₀ (fun p _ => Nat.cast_nonneg p) (fun p hp => (hP p hp).2)
      _ = Real.exp (A*(U.card:ℝ)) := by rw [prod_const,← Real.rpow_natCast,Real.exp_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        rw [mul_comm A]
        exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hr) hA)
  · intro p hp
    have hpP := Nat.prime_of_mem_primesLE hp
    have hpW : (p:ℝ) ≤ W := (Nat.cast_le.mpr (Nat.mem_primesLE.mp hp).1).trans
      (Nat.floor_le (Real.exp_pos _).le)
    change p.Coprime (∏ q∈U,q)
    apply Nat.Coprime.prod_right
    intro q hq
    apply hpP.coprime_iff_not_dvd.mpr
    intro hd
    have he := (Nat.dvd_prime (hP q hq).1).mp hd |>.resolve_left hpP.ne_one
    exact (not_lt_of_ge (he ▸ hpW)) (hbig q (hU hq))

theorem giant_candidate_actual_rough_full_dyad_ratio_eventually (τ A : ℝ)
    (hτ : 0 < τ) (hA : 0 ≤ A) (r : ℕ) :
    ∀ᶠ x : ℝ in atTop,∀ U : Finset ℕ,U ⊆ giantCandidateFullPrimes x → U.card≤r →
      let Q := giantCandidateResidueModulus U
      ∀ (H : ℕ) (a : ZMod Q),x^τ≤(H:ℝ) →
      let W := Real.exp ((Real.log x)^(6/25:ℝ))
      let V := markedSieveEulerProduct W
      let B := giantCandidateRoughFullDyad W H
      (H:ℝ)*V/2 ≤ (B.card:ℝ) ∧ (B.card:ℝ) ≤ 2*((H:ℝ)*V) ∧
      |(Q:ℝ)*((B.filter (fun n : ℕ => (n:ZMod Q)=a)).card:ℝ)/(B.card:ℝ)-1| ≤ (Real.log x)^(-A) := by
  filter_upwards [giantCandidateActualResidueModulus_eventually r,
    giant_candidate_rough_full_dyad_ratio_eventually τ (r:ℝ) A hτ (Nat.cast_nonneg _) hA]
    with x hmod hratio
  intro U hU hr Q H a hH
  obtain ⟨hQ,hQhi,hcop⟩ := hmod U hU hr
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have h := hratio H Q a.val hQ hQhi hcop hH
  simpa only [giantCandidateFullDyad_residue_eq_zmod] using h

end
end ArtinMatthews
