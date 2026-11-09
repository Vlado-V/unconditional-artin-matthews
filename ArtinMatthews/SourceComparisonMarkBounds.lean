module

public import ArtinMatthews.SourceComparisonDivisorL2
public import ArtinMatthews.SourceComparisonSmallMark


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed damping gives pointwise bounds for the actual ordered weights,
including the reduced zero-count group. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

private theorem damped_power_count_bound (u t : ℕ) (ht : t ≤ u) {r : ℝ}
    (hr : 0 < r) (hr₁ : r < 1) :
    r ^ (u - t) * (u : ℝ) ^ t ≤ (t.factorial : ℝ) / (r * (-Real.log r)) ^ t := by
  let a := -Real.log r
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hr hr₁)
  have hfac : 0 < (t.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos t
  have hb := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (a * (u : ℝ))
    (mul_nonneg ha.le (Nat.cast_nonneg _)) t)
  have hrpow : r ^ u = Real.exp (-(a * (u : ℝ))) := by
    rw [← Real.exp_log hr, ← Real.exp_nat_mul]
    congr 1
    unfold a
    ring
  have hp : r ^ (u - t) * r ^ t = r ^ u := by
    rw [← pow_add, Nat.sub_add_cancel ht]
  apply (le_div_iff₀ (pow_pos (mul_pos hr ha) t)).mpr
  calc
    _ = r ^ u * (a * (u : ℝ)) ^ t := by
      rw [← hp, mul_pow, mul_pow]
      ring
    _ ≤ r ^ u * (Real.exp (a * (u : ℝ)) * (t.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg hr.le _)
    _ = _ := by
      rw [hrpow, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

def sourceComparisonMarkDampedMass (P : G → Finset ℕ) (t : G → ℕ) (r : ℝ) : ℝ :=
  sourceComparisonMarkFactorialMass P t / (r * (-Real.log r)) ^ (∑ g, t g)

theorem sourceComparisonMarkWeight_damped_bound (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1)
    (hV : ∀ g, 0 < bandReciprocalMass (P g))
    {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ r) (n : ℕ) :
    ‖sourceComparisonMarkWeight P t q b n‖ ≤ sourceComparisonMarkDampedMass P t r := by
  classical
  let V := sourceComparisonMarkMass P t
  let D := sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t
  let a := r * (-Real.log r)
  have ha : 0 < a := mul_pos hr (neg_pos.mpr (Real.log_neg hr hr₁))
  have hV₀ : 0 < V := sourceComparisonMarkMass_pos P t hV
  have hA : 0 ≤ sourceComparisonMarkDampedMass P t r := by
    unfold sourceComparisonMarkDampedMass sourceComparisonMarkFactorialMass
    exact div_nonneg (div_nonneg (prod_nonneg (fun _ _ => Nat.cast_nonneg _)) hV₀.le)
      (pow_nonneg ha.le _)
  by_cases hD : D.Nonempty
  · obtain ⟨l, hl⟩ := hD
    have hlist := (mem_sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t l).mp hl
    have ht (g : G) : t g ≤ bandCount (P g) n := by
      have hs := card_le_card (representedChoiceSet_subset (hlist.1 g))
      rw [representedChoiceSet, card_image_of_injective _ (hlist.2 g), card_univ, Fintype.card_fin] at hs
      exact hs
    have hsum : ‖∑ l ∈ D, b l‖ ≤ (D.card : ℝ) := by
      apply (norm_sum_le _ _).trans
      have hsub : D ⊆ sourceComparisonMarkChoices P t := by
        change sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t ⊆ _
        rw [sourceComparisonMarkChoices_active_filter]
        exact filter_subset _ _
      exact (sum_le_sum (fun l hl => hb l (hsub hl))).trans_eq (by simp)
    have hc : (D.card : ℝ) ≤ ∏ g, (bandCount (P g) n : ℝ) ^ t g := by
      have hcard : D.card ≤ ∏ g, bandCount (P g) n ^ t g := by
        unfold D sourceComparisonMarkChoices
        apply (card_filter_le _ _).trans_eq
        simp only [representedArrayChoices, Fintype.card_piFinset, prod_const, card_univ,
          Fintype.card_fin, bandCount]
      exact_mod_cast hcard
    have hqD : 0 ≤ sourceComparisonMarkHitDamping P t q n :=
      prod_nonneg (fun g _ => pow_nonneg (hq g).1 _)
    unfold sourceComparisonMarkWeight
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hqD, Real.norm_of_nonneg hV₀.le]
    calc
      _ ≤ (sourceComparisonMarkHitDamping P t q n *
          ∏ g, (bandCount (P g) n : ℝ) ^ t g) / V :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsum.trans hc) hqD) hV₀.le
      _ = (∏ g, ((q g) ^ (bandCount (P g) n - t g) * (bandCount (P g) n : ℝ) ^ t g)) / V := by
        rw [sourceComparisonMarkHitDamping, prod_mul_distrib]
      _ ≤ (∏ g, ((t g).factorial : ℝ) / a ^ t g) / V := by
        apply div_le_div_of_nonneg_right _ hV₀.le
        apply prod_le_prod₀ (fun g _ => mul_nonneg (pow_nonneg (hq g).1 _) (pow_nonneg (Nat.cast_nonneg _) _))
        intro g _
        apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hq g).1 (hq g).2 _)
          (pow_nonneg (Nat.cast_nonneg _) _)).trans
        exact damped_power_count_bound _ _ (ht g) hr hr₁
      _ = _ := by
        rw [prod_div_distrib, prod_pow_eq_pow_sum, sourceComparisonMarkDampedMass,
          sourceComparisonMarkFactorialMass]
        unfold a V
        ring
  · have he : D = ∅ := not_nonempty_iff_eq_empty.mp hD
    unfold sourceComparisonMarkWeight
    change ‖(sourceComparisonMarkHitDamping P t q n : ℂ) * (∑ l ∈ D, b l) / (V : ℂ)‖ ≤ _
    simpa only [he, sum_empty, mul_zero, zero_div, norm_zero] using hA

end
end ArtinMatthews
