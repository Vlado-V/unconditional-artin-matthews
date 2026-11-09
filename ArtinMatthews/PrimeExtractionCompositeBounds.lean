module

public import ArtinMatthews.PrimeExtractionCompositeCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! Uniform bounds for the finite composite expansion, including the
temporarily allowed repeated-prime tuples. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators

theorem roughPrimeTupleCoefficient_div_factorial_norm_le (a : ℕ → ℂ) (j n : ℕ) (z : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p : ℕ, p.Prime → z < (p : ℝ) → ‖a p‖ ≤ C) :
    ‖roughPrimeTupleCoefficient a j n z / j.factorial‖ ≤ C ^ j := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos j : (0 : ℝ) < j.factorial)).mpr
  simpa only [mul_comm] using roughPrimeTupleCoefficient_norm_le a j n z hC ha

theorem roughCompositeCoefficient_norm_le (a : ℕ → ℂ) (J n : ℕ) (z : ℝ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ p : ℕ, p.Prime → z < (p : ℝ) → ‖a p‖ ≤ C) :
    ‖roughCompositeCoefficient a J n z‖ ≤ ∑ j ∈ Finset.Icc 2 J, C ^ j :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
    roughPrimeTupleCoefficient_div_factorial_norm_le a j n z hC ha)

theorem roughCompositeCoefficient_eq_zero_of_not_rough (a : ℕ → ℂ) (J n : ℕ) (z : ℝ)
    (hn : ¬MarkedRoughAbove z n) : roughCompositeCoefficient a J n z = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hj : roughPrimeTupleCoefficient a j n z = 0 := by
    by_contra h
    exact hn (roughPrimeTupleCoefficient_support a j n z h).2.1
  rw [hj, zero_div]

noncomputable def actualCompositeThetaCoefficient (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  if n ≠ 1 ∧ ¬n.Prime then idealThetaCoeff η n * χ n else 0

theorem actualCompositeThetaCoefficient_norm_le (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖actualCompositeThetaCoefficient η χ n‖ ≤ ‖idealThetaCoeff η n * χ n‖ := by
  unfold actualCompositeThetaCoefficient
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (idealThetaCoeff η n * χ n)

/-- The exact composite expansion agrees off the actual nonsquarefree set,
and the discrepancy is uniformly bounded on rough support. -/
theorem actualCompositeTheta_expansion_bounds_eventually (η : HeckeFamily.Character)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) {γ : ℝ} (hγ : 0 < γ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ T * x →
      MarkedRoughAbove (x ^ γ) n →
      (Squarefree n → actualCompositeThetaCoefficient η χ n =
        roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ)) ∧
      ‖actualCompositeThetaCoefficient η χ n -
        roughCompositeCoefficient (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ)‖ ≤
          (2 : ℝ) ^ ⌈2 / γ⌉₊ + ∑ j ∈ Finset.Icc 2 ⌈2 / γ⌉₊, (2 : ℝ) ^ j := by
  filter_upwards [marked_rough_factor_and_divisor_count_eventually T hγ,
    idealThetaCoeff_rough_bound_eventually T hγ] with x hf hc
  intro n hn hnT hrough
  refine ⟨?_, ?_⟩
  · intro hsq
    exact (roughThetaCompositeCoefficient_eq η χ _ hsq hrough (hf n hn hnT hrough).1).symm
  · have htuple := roughCompositeCoefficient_norm_le
      (fun p => idealThetaCoeff η p * χ p) ⌈2 / γ⌉₊ n (x ^ γ) (by norm_num : (0 : ℝ) ≤ 2)
      (fun p hp _ => by
        rw [norm_mul]
        exact (mul_le_mul (idealThetaCoeff_prime_norm_le_two η hp) (χ.norm_le_one _)
          (norm_nonneg _) (by norm_num)).trans (by norm_num))
    exact (norm_sub_le _ _).trans (add_le_add
      ((actualCompositeThetaCoefficient_norm_le η χ n).trans (hc n hn hnT hrough η q χ)) htuple)

end ArtinMatthews
