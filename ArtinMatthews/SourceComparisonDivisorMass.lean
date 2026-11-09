module

public import ArtinMatthews.SourceComparisonMarkedDivisors
public import ArtinMatthews.MarkedProgressionWeightedLoss


set_option backward.privateInPublic true
@[expose] public section

/-! Reciprocal coefficient mass uses the actual harmonic list normalizers.
The unnormalized mass follows from the same divisor support bound. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

theorem sourceComparisonMarkMass_pos (P : G → Finset ℕ) (t : G → ℕ)
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) : 0 < sourceComparisonMarkMass P t :=
  prod_pos (fun g _ => pow_pos (hV g) _)

private theorem choices_reciprocal_sum (P : G → Finset ℕ) (t : G → ℕ) :
    (∑ l ∈ representedArrayChoices P t, ∏ g, ∏ i : Fin (t g), 1 / (l g i : ℝ)) =
      sourceComparisonMarkMass P t := by
  classical
  have hg (g : G) : bandReciprocalMass (P g) ^ t g =
      ∑ l ∈ Fintype.piFinset (fun _ : Fin (t g) => P g), ∏ i : Fin (t g), 1 / (l i : ℝ) := by
    have h := prod_univ_sum (fun _ : Fin (t g) => P g) (fun _ (p : ℕ) => 1 / (p : ℝ))
    simpa only [bandReciprocalMass, prod_const, card_univ, Fintype.card_fin] using h
  unfold sourceComparisonMarkMass
  simp_rw [hg]
  exact (prod_univ_sum (fun g => Fintype.piFinset (fun _ : Fin (t g) => P g))
    (fun g l => ∏ i : Fin (t g), 1 / (l i : ℝ))).symm

private theorem choice_reciprocal_eq (P : G → Finset ℕ) (t : G → ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    {l : (g : G) → Fin (t g) → ℕ} (hl : l ∈ sourceComparisonMarkChoices P t) :
    1 / ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ) =
      ∏ g, ∏ i : Fin (t g), 1 / (l g i : ℝ) := by
  classical
  obtain ⟨hm, hi⟩ := (mem_sourceComparisonMarkChoices P t l).mp hl
  have hp : Set.PairwiseDisjoint (↑(univ : Finset G)) (fun g => representedChoiceSet (l g)) :=
    fun g _ j _ hgj => (hdis hgj).mono (representedChoiceSet_subset (hm g))
      (representedChoiceSet_subset (hm j))
  have he : 1 / (∏ p ∈ representedArraySelected l, (p : ℝ)) =
      ∏ p ∈ representedArraySelected l, 1 / (p : ℝ) := by rw [prod_div_distrib, prod_const_one]
  rw [Nat.cast_prod, he]
  unfold representedArraySelected
  rw [prod_biUnion hp]
  apply prod_congr rfl
  intro g _
  unfold representedChoiceSet
  exact prod_image (fun _ _ _ _ h => hi g h)

theorem sourceComparisonMarkCoefficient_reciprocal_le_one (P : G → Finset ℕ) (t : G → ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) :
    (∑ l ∈ sourceComparisonMarkChoices P t,
      ‖sourceComparisonMarkCoefficient P t b l‖ /
        ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ)) ≤ 1 := by
  classical
  let V := sourceComparisonMarkMass P t
  have hV₀ : 0 < V := sourceComparisonMarkMass_pos P t hV
  calc
    _ ≤ ∑ l ∈ sourceComparisonMarkChoices P t,
        (∏ g, ∏ i : Fin (t g), 1 / (l g i : ℝ)) / V := by
      apply sum_le_sum
      intro l hl
      rw [sourceComparisonMarkCoefficient, norm_div, Complex.norm_real,
        Real.norm_of_nonneg hV₀.le]
      have hr := choice_reciprocal_eq P t hdis hl
      calc
        _ = (‖b l‖ / V) * (1 / ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ)) := by ring
        _ ≤ (1 / V) * (1 / ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hb l hl) hV₀.le) (by positivity)
        _ = _ := by rw [hr]; ring
    _ ≤ ∑ l ∈ representedArrayChoices P t,
        (∏ g, ∏ i : Fin (t g), 1 / (l g i : ℝ)) / V := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      exact fun _ _ _ => by positivity
    _ = 1 := by rw [← sum_div, choices_reciprocal_sum, div_self hV₀.ne']

private theorem weighted_abs_reciprocal_le_exp (P S : Finset ℕ) (k : ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) :
    (∑ i ∈ markedWeightedIndices P S k,
      |markedWeightedCoefficient θ i| / (markedWeightedDivisor S i : ℝ)) ≤
        (1 / ((∏ p ∈ S, p : ℕ) : ℝ)) * Real.exp (∑ p ∈ P, 1 / (p : ℝ)) := by
  classical
  have hmass : (∑ p ∈ P \ S, θ p / (p : ℝ)) ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
    apply (sum_le_sum (g := fun p : ℕ => 1 / (p : ℝ)) fun p hp =>
      div_le_div_of_nonneg_right (hθ p (mem_sdiff.mp hp).1).2 (Nat.cast_nonneg p)).trans
    exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => by positivity)
  apply le_trans _ (marked_weighted_selected_partial_reciprocal_mass_le_exp P S k θ
    (fun p hp => (hθ p hp).1) hmass)
  unfold markedWeightedIndices markedWeightedCoefficient markedWeightedDivisor
  rw [sum_sigma]
  apply sum_le_sum
  intro j _
  apply sum_le_sum
  intro T hT
  have hT₀ : 0 ≤ ∏ p ∈ T, θ p := prod_nonneg (fun p hp =>
    (hθ p (mem_sdiff.mp ((mem_powersetCard.mp hT).1 hp)).1).1)
  simp [abs_mul, abs_pow, abs_of_nonneg hT₀]

theorem sourceComparisonDivisorCoefficient_reciprocal_bound (P : G → Finset ℕ)
    (t : G → ℕ) (q : G → ℝ) (k : ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) :
    (∑ i ∈ sourceComparisonDivisorIndices P t k,
      ‖sourceComparisonDivisorCoefficient P t q b i‖ / (sourceComparisonDivisor i : ℝ)) ≤
      Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) := by
  classical
  let E := Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ))
  unfold sourceComparisonDivisorIndices
  rw [sum_sigma]
  calc
    _ ≤ ∑ l ∈ sourceComparisonMarkChoices P t,
        (‖sourceComparisonMarkCoefficient P t b l‖ /
          ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ)) * E := by
      apply sum_le_sum
      intro l _
      simp only [sourceComparisonDivisorCoefficient, sourceComparisonDivisor, norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      simp_rw [mul_div_assoc]
      rw [← mul_sum]
      exact (mul_le_mul_of_nonneg_left
        (weighted_abs_reciprocal_le_exp _ _ k _
          (fun _ hp => sourceComparisonMarkResidualDamping_bounds P q hdis hq hp))
        (norm_nonneg _)).trans_eq (by ring)
    _ = (∑ l ∈ sourceComparisonMarkChoices P t,
        ‖sourceComparisonMarkCoefficient P t b l‖ /
          ((∏ p ∈ representedArraySelected l, p : ℕ) : ℝ)) * E := (sum_mul ..).symm
    _ ≤ _ := by
      have hE : 0 ≤ E := (Real.exp_pos _).le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (sourceComparisonMarkCoefficient_reciprocal_le_one P t hdis hV b hb) hE

theorem sourceComparisonDivisorCoefficient_mass_bound (P : G → Finset ℕ)
    (t : G → ℕ) (q : G → ℝ) (k : ℕ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1)
    {Z : ℝ} (hZ : 1 ≤ Z) (hpZ : ∀ p ∈ univ.biUnion P, (p : ℝ) ≤ Z) :
    (∑ i ∈ sourceComparisonDivisorIndices P t k, ‖sourceComparisonDivisorCoefficient P t q b i‖) ≤
      Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) * Z ^ ((∑ g, t g) + k) := by
  calc
    _ ≤ ∑ i ∈ sourceComparisonDivisorIndices P t k,
        (‖sourceComparisonDivisorCoefficient P t q b i‖ / (sourceComparisonDivisor i : ℝ)) *
          Z ^ ((∑ g, t g) + k) := by
      apply sum_le_sum
      intro i hi
      have hd : (0 : ℝ) < sourceComparisonDivisor i := by
        exact_mod_cast sourceComparisonDivisor_pos P t k hP hi
      calc
        _ = (‖sourceComparisonDivisorCoefficient P t q b i‖ / (sourceComparisonDivisor i : ℝ)) *
            (sourceComparisonDivisor i : ℝ) := (div_mul_cancel₀ _ hd.ne').symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sourceComparisonDivisor_bound P t k hZ hpZ hi)
          (div_nonneg (norm_nonneg (sourceComparisonDivisorCoefficient P t q b i)) hd.le)
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sourceComparisonDivisorCoefficient_reciprocal_bound P t q k hdis hV hq b hb)
        (pow_nonneg (zero_le_one.trans hZ) _)

end
end ArtinMatthews
