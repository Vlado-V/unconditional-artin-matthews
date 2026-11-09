module

public import ArtinMatthews.SourceComparisonMarkBounds


set_option backward.privateInPublic true
@[expose] public section

/-! A uniformly positive reciprocal mass per group bounds every fixed
mark-depth cost exponentially in the number of groups. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

universe v
variable {G : Type v} [Fintype G]

theorem sourceComparisonMarkFactorialMass_nonneg (P : G → Finset ℕ) (t : G → ℕ)
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) :
    0 ≤ sourceComparisonMarkFactorialMass P t := by
  unfold sourceComparisonMarkFactorialMass
  exact div_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _) (sourceComparisonMarkMass_pos P t hV).le

theorem sourceComparisonMarkUnionMass_le_card (P : G → Finset ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hV : ∀ g, bandReciprocalMass (P g) ≤ 1) :
    (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) ≤ (Fintype.card G : ℝ) := by
  classical
  rw [sum_biUnion (fun _ _ _ _ hij => hdis hij)]
  exact (sum_le_sum (fun g _ => hV g)).trans_eq (by simp)

private theorem scaledFactorialMass_le (P : G → Finset ℕ) (t : G → ℕ) (m : ℕ)
    (ht : ∀ g, t g ≤ m) {v a : ℝ} (hv : 0 < v) (ha : 0 < a)
    (hV : ∀ g, v ≤ bandReciprocalMass (P g)) :
    sourceComparisonMarkFactorialMass P t / a ^ (∑ g, t g) ≤
      ((m.factorial : ℝ) * (max 1 ((v * a)⁻¹)) ^ m) ^ Fintype.card G := by
  let B := (m.factorial : ℝ) * (max 1 ((v * a)⁻¹)) ^ m
  have hm : 1 ≤ max 1 ((v*a)⁻¹) := le_max_left _ _
  have hprod :
      sourceComparisonMarkFactorialMass P t / a ^ (∑ g, t g) =
        ∏ g, ((t g).factorial : ℝ) / (bandReciprocalMass (P g) * a) ^ t g := by
    unfold sourceComparisonMarkFactorialMass sourceComparisonMarkMass
    simp_rw [mul_pow]
    rw [prod_div_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, div_div]
  rw [hprod]
  calc
    _ ≤ ∏ _g : G, B := by
      apply prod_le_prod₀ (fun g _ => div_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (mul_nonneg (hv.le.trans (hV g)) ha.le) _))
      intro g _
      have hVa : 0 < bandReciprocalMass (P g) * a :=
        mul_pos (hv.trans_le (hV g)) ha
      have hV' : v * a ≤ bandReciprocalMass (P g) * a :=
        mul_le_mul_of_nonneg_right (hV g) ha.le
      have hi : (bandReciprocalMass (P g) * a)⁻¹ ≤ max 1 ((v*a)⁻¹) :=
        (inv_anti₀ (mul_pos hv ha) hV').trans (le_max_right _ _)
      unfold B
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_le_mul (Nat.cast_le.mpr (Nat.factorial_le (ht g)))
        ((pow_le_pow_left₀ (inv_nonneg.mpr hVa.le)
          hi _).trans (pow_le_pow_right₀ hm (ht g)))
        (pow_nonneg (inv_nonneg.mpr hVa.le) _) (Nat.cast_nonneg _)
    _ = _ := by simp [B]

private theorem comparison_log_card_power {B L E : ℝ} (hB : 1 ≤ B) (hL : 0 < L)
    {N : ℕ} (hN : (N : ℝ) ≤ E * Real.log L) :
    B ^ N ≤ L ^ (E * Real.log B) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (zero_lt_one.trans_le hB), Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  exact (mul_le_mul_of_nonneg_left hN (Real.log_nonneg hB)).trans_eq (by ring)

theorem sourceComparisonMarkMass_log_bounds (m : ℕ) {v r E : ℝ}
    (hv : 0 < v) (hr : 0 < r) (hr₁ : r < 1) (hE : 0 ≤ E) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {G : Type v} [Fintype G] (P : G → Finset ℕ) (t : G → ℕ),
      (∀ g, t g ≤ m) → (∀ g, v ≤ bandReciprocalMass (P g)) →
      ∀ L : ℝ, 1 ≤ L → (Fintype.card G : ℝ) ≤ E * Real.log L →
        sourceComparisonMarkFactorialMass P t ≤ L ^ D ∧
        sourceComparisonMarkDampedMass P t r ≤ L ^ D := by
  let a := r * (-Real.log r)
  have ha : 0 < a := mul_pos hr (neg_pos.mpr (Real.log_neg hr hr₁))
  let B (a : ℝ) := (m.factorial : ℝ) * (max 1 ((v*a)⁻¹)) ^ m
  have hB (a : ℝ) : 1 ≤ B a := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos m) (one_le_pow₀ (le_max_left _ _))
  let D := max (E * Real.log (B 1)) (E * Real.log (B a))
  refine ⟨D, (mul_nonneg hE (Real.log_nonneg (hB 1))).trans (le_max_left _ _), ?_⟩
  intro G _ P t ht hV L hL hN
  have hf : sourceComparisonMarkFactorialMass P t ≤ B 1 ^ Fintype.card G := by
    simpa [B] using scaledFactorialMass_le P t m ht hv (zero_lt_one : (0:ℝ)<1) hV
  have hd : sourceComparisonMarkDampedMass P t r ≤ B a ^ Fintype.card G :=
    scaledFactorialMass_le P t m ht hv ha hV
  exact ⟨(hf.trans (comparison_log_card_power (hB 1) (zero_lt_one.trans_le hL) hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)),
    (hd.trans (comparison_log_card_power (hB a) (zero_lt_one.trans_le hL) hN)).trans
      (Real.rpow_le_rpow_of_exponent_le hL (le_max_right _ _))⟩

end
end ArtinMatthews
