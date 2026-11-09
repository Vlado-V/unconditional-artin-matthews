module

public import ArtinMatthews.SourceComparisonDivisorL2


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed power moment for the literal normalized marked endpoint.
The ordered-list test remains arbitrary in the closed unit disk. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

private theorem comparisonMarkChoices_card_le_exp
    (P : G → Finset ℕ) (t : G → ℕ) (n : ℕ)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) :
    ((sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t).card:ℝ) ≤
      (∏ g, ((t g).factorial:ℝ))*Real.exp (bandCount (univ.biUnion P) n) := by
  classical
  have hc : (sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t).card ≤
      ∏ g, (bandCount (P g) n)^t g := by
    unfold sourceComparisonMarkChoices
    apply (card_filter_le _ _).trans_eq
    simp only [representedArrayChoices,Fintype.card_piFinset,prod_const,card_univ,
      Fintype.card_fin,bandCount]
  calc
    _ ≤ ∏ g, ((bandCount (P g) n:ℝ))^t g := by exact_mod_cast hc
    _ ≤ _ := by
      rw [giantCandidateBandCount_union P hdis,Nat.cast_sum,Real.exp_sum,← prod_mul_distrib]
      apply prod_le_prod₀ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _)
      intro g _
      have hf : 0 < ((t g).factorial:ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact ((div_le_iff₀ hf).mp
        (Real.pow_div_factorial_le_exp (bandCount (P g) n:ℝ) (Nat.cast_nonneg _) (t g))).trans_eq
          (mul_comm _ _)

theorem sourceComparisonMarkWeight_norm_le_hit_exp
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1) (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) (n : ℕ) :
    ‖sourceComparisonMarkWeight P t q b n‖ ≤
      sourceComparisonMarkFactorialMass P t*Real.exp (bandCount (univ.biUnion P) n) := by
  let D := sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t
  have hd0 : 0 ≤ sourceComparisonMarkHitDamping P t q n := by
    unfold sourceComparisonMarkHitDamping
    exact prod_nonneg (fun g _ => pow_nonneg (hq g).1 _)
  have hd1 : sourceComparisonMarkHitDamping P t q n ≤ 1 := by
    unfold sourceComparisonMarkHitDamping
    exact prod_le_one₀ (fun g _ => pow_nonneg (hq g).1 _)
      (fun g _ => pow_le_one₀ (hq g).1 (hq g).2)
  have hV0 := sourceComparisonMarkMass_pos P t hV
  have hs : ‖∑ l ∈ D, b l‖ ≤ (D.card:ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _l ∈ D, (1:ℝ) := by
        apply sum_le_sum
        intro l hl
        change l ∈ sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t at hl
        rw [sourceComparisonMarkChoices_active_filter] at hl
        exact hb l (mem_filter.mp hl).1
      _ = _ := by simp
  unfold sourceComparisonMarkWeight sourceComparisonMarkFactorialMass
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg hd0,Complex.norm_real,
    Real.norm_of_nonneg hV0.le]
  change sourceComparisonMarkHitDamping P t q n*‖∑ l ∈ D, b l‖ / sourceComparisonMarkMass P t ≤ _
  calc
    _ ≤ (D.card:ℝ)/sourceComparisonMarkMass P t := by
      exact div_le_div_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul hd1 hs (norm_nonneg _) zero_le_one) hV0.le
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (comparisonMarkChoices_card_le_exp P t n hdis) hV0.le

/-- The source cutoff, amplitude and normalized distinct mark weight
are all evaluated at the same endpoint. -/
def giantComparisonWeightedEndpoint
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (ψ : ℝ → ℂ)
    (F : ℕ → ℂ) (Y : ℝ) (n : ℕ) : ℂ :=
  ψ ((n:ℝ)/Y)*F n*sourceComparisonMarkWeight P t q b n

theorem giantComparisonWeightedEndpoint_power_sum_le
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1) (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1)
    (ψ : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hψ : ∀ z, ‖ψ z‖ ≤ M)
    (F : ℕ → ℂ) (Y : ℝ) (k N : ℕ) (Z : Finset ℕ) (hZ : Z ⊆ Ioc 0 N) :
    (∑ n ∈ Z, ‖giantComparisonWeightedEndpoint P t q b ψ F Y n‖^k) ≤
      M^k*(sourceComparisonMarkFactorialMass P t)^k *
      ((∑ n ∈ Z, ‖F n‖^(2*k)) + (N:ℝ)*Real.exp
        ((Real.exp (2*(k:ℝ))-1)*∑ p ∈ univ.biUnion P, 1/(p:ℝ))) := by
  let A := sourceComparisonMarkFactorialMass P t
  let B := Real.exp (2*(k:ℝ))
  let Q := univ.biUnion P
  have hA : 0 ≤ A := by
    unfold A sourceComparisonMarkFactorialMass
    exact div_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _)
      (sourceComparisonMarkMass_pos P t hV).le
  have hB : 1 ≤ B := Real.one_le_exp_iff.mpr (by positivity)
  have hpoint (n : ℕ) :
      ‖giantComparisonWeightedEndpoint P t q b ψ F Y n‖^k ≤
        M^k*A^k*(‖F n‖^(2*k)+B^bandCount Q n) := by
    let E := Real.exp (bandCount Q n)
    have hE : 0 ≤ E := (Real.exp_pos _).le
    have hnorm : ‖giantComparisonWeightedEndpoint P t q b ψ F Y n‖ ≤ M*‖F n‖*(A*E) := by
      unfold giantComparisonWeightedEndpoint
      rw [norm_mul,norm_mul]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hψ _) (norm_nonneg _))
        (sourceComparisonMarkWeight_norm_le_hit_exp P t q hdis hq hV b hb n)
        (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
    have hexp : E^(2*k) = B^bandCount Q n := by
      unfold E B
      rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    calc
      _ ≤ (M*‖F n‖*(A*E))^k := pow_le_pow_left₀ (norm_nonneg _) hnorm _
      _ = M^k*A^k*(‖F n‖^k*E^k) := by simp only [mul_pow]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hM _) (pow_nonneg hA _))
        rw [← hexp,mul_comm 2 k,pow_mul,pow_mul]
        nlinarith only [sq_nonneg (‖F n‖^k-E^k),mul_nonneg (pow_nonneg (norm_nonneg (F n)) k)
          (pow_nonneg hE k)]
  calc
    _ ≤ ∑ n ∈ Z, M^k*A^k*(‖F n‖^(2*k)+B^bandCount Q n) :=
      sum_le_sum (fun n _ => hpoint n)
    _ = M^k*A^k*((∑ n ∈ Z, ‖F n‖^(2*k)) + ∑ n ∈ Z, B^bandCount Q n) := by
      rw [← mul_sum,sum_add_distrib]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hM _) (pow_nonneg hA _))
      apply add_le_add le_rfl
      exact (sum_le_sum_of_subset_of_nonneg hZ (fun _ _ _ => pow_nonneg (zero_le_one.trans hB) _)).trans
        (sourceComparisonHitMoment_le Q hP hB N)

end
end ArtinMatthews
