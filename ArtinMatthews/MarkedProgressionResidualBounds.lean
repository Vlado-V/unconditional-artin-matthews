module

public import ArtinMatthews.MarkedProgressionResidual
public import ArtinMatthews.MarkedProgressionWeightedLoss


set_option backward.privateInPublic true
@[expose] public section

/-! Explicit mass bounds for the finite selected-residual progression
estimate. The only quantities left are band size, lower prime endpoint,
reciprocal mass, truncation depth, and the actual represented divisor. -/

namespace ArtinMatthews

open MeasureTheory

open OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

/-- The positive omitted layer has at most the full ordered-choice mass. -/
theorem markedWeightedTailCoefficientMass_le (P S : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (k : ℕ) :
    markedWeightedTailCoefficientMass P S θ k ≤ (max 1 ((P \ S).card : ℝ)) ^ k := by
  unfold markedWeightedTailCoefficientMass
  calc
    _ ≤ ∑ _T ∈ (P \ S).powersetCard k, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro T hT
      have ht (p : ℕ) (hp : p ∈ T) :=
        hθ p (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1
      exact Finset.prod_le_one₀ (fun p hp => (ht p hp).1) (fun p hp => (ht p hp).2)
    _ = ((P \ S).card.choose k : ℝ) := by simp [Finset.card_powersetCard]
    _ ≤ ((P \ S).card : ℝ) ^ k := by exact_mod_cast Nat.choose_le_pow (P \ S).card k
    _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right _ _) k

/-- The positive omitted reciprocal mass has factorial decay. -/
theorem markedWeightedTailModel_le (P S : Finset ℕ) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p) (k : ℕ) {V : ℝ} (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V) :
    markedWeightedTailModel P S θ k ≤
      (1 / (∏ p ∈ S, p : ℕ)) * (V ^ k / k.factorial) := by
  unfold markedWeightedTailModel
  rw [marked_weighted_selected_reciprocal_mass]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact BonferroniDensity.elementarySum_le_pow_div_factorial (P \ S)
    (fun p => θ p / (p : ℝ))
    (fun p hp => div_nonneg (hθ p (Finset.mem_sdiff.mp hp).1) (Nat.cast_nonneg _)) hV hmass k

/-- The retained coprimality loss keeps its true represented reciprocal
factor, independent of the number of available prime choices. -/
theorem markedWeightedLocalMass_le (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p) (k : ℕ) {y V : ℝ} (hy : 0 < y)
    (hmin : ∀ p ∈ P, y ≤ (p : ℝ))
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V) :
    markedWeightedLocalMass P S θ k ≤
      (((S.card + k : ℕ) : ℝ) / y) * (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V := by
  classical
  unfold markedWeightedLocalMass markedWeightedIndices markedWeightedCoefficient markedWeightedDivisor
  rw [Finset.sum_sigma]
  have heq : (∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      (|(-1 : ℝ) ^ j * ∏ p ∈ T, θ p| / (∏ p ∈ S ∪ T, p : ℕ)) *
        ∑ q ∈ (∏ p ∈ S ∪ T, p : ℕ).primeFactors, 1 / (q : ℝ)) =
      ∑ j ∈ Finset.range (k + 1), ∑ T ∈ (P \ S).powersetCard j,
      ((∏ p ∈ T, θ p) / (∏ p ∈ S ∪ T, p : ℕ)) *
        ∑ q ∈ (∏ p ∈ S ∪ T, p : ℕ).primeFactors, 1 / (q : ℝ) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro T hT
    have ht : 0 ≤ ∏ p ∈ T, θ p := Finset.prod_nonneg (fun p hp =>
      hθ p (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hT).1 hp)).1)
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg ht]
  rw [heq]
  exact marked_weighted_selected_truncated_local_loss_le P S hP hS k θ hθ hy hmin hmass

/-- Quantitative finite selected-residual remainder with every coefficient
quantity discharged. The denominator is the actual represented union. -/
theorem marked_weighted_residual_quantitative (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) (hf0 : ∀ t, 0 ≤ f t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
          f u * markedWeightedResidual P S θ u) -
        ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  have h0 := marked_weighted_residual_summed_error P S hP hS θ hθ m R f hT hf hderiv hfT hf0
  have hC := markedWeightedCoefficient_mass_le P S θ hθ (2 * m)
  have hD := markedWeightedTailCoefficientMass_le P S θ hθ (2 * m + 1)
  have hL := markedWeightedLocalMass_le P S hP hS θ (fun p hp => (hθ p hp).1) (2 * m)
    hy hmin hmass
  have hM := markedWeightedTailModel_le P S θ (fun p hp => (hθ p hp).1)
    (2 * m + 1) hV hmass
  have hI : 0 ≤ ∫ t in Set.Ioc 0 T, f t := MeasureTheory.integral_nonneg hf0
  have hVar : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv f t| :=
    MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  have hH : 0 ≤ (harmonic R : ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg (fun r _ => by positivity)
  apply h0.trans
  calc
    _ ≤ (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * (1 / (∏ p ∈ S, p : ℕ)) * Real.exp V +
          2 * ((1 / (∏ p ∈ S, p : ℕ)) * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (add_le_add hC hD) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (add_le_add hL (mul_le_mul_of_nonneg_left hM (by norm_num))) (mul_nonneg hI hH)
    _ = _ := by ring

/-- Exact scale-`x` version used by the marked predecessor progression
estimate. Only the main integral acquires a factor of `x`. -/
theorem marked_weighted_residual_rescaled_quantitative (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
          Φ ((u : ℝ) / x) * markedWeightedResidual P S θ u) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
          (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) +
      ((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((S.card + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
  have h := marked_weighted_residual_quantitative P S hP hS θ hθ m R hy hmin hV hmass
    (fun u => Φ (u / x)) (mul_nonneg hT hx.le) (marked_rescale_differentiable Φ x hΦ)
    (marked_rescale_deriv_continuous Φ x hΦ hderiv)
    (by rw [marked_rescale_endpoint Φ hx T, hΦT]) (fun u => hΦ0 (u / x))
  rw [marked_rescale_integral Φ hx hT, marked_rescale_variation Φ hx hT hΦ] at h
  exact h

end ArtinMatthews
