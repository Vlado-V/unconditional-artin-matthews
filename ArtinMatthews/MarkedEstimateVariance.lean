module

public import ArtinMatthews.MarkedEstimateArrayModel
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Variance decay for independent marking arrays

All expectations here are finite sums with the actual product probability
mass. Independence is proved by finite sum/product distributivity; no
covariance or variance estimate is taken as an analytic hypothesis.
-/

namespace ArtinMatthews

open scoped BigOperators

noncomputable def finiteProductMass {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} (μ : ∀ i, Ω i → ℝ) (x : ∀ i, Ω i) : ℝ :=
  ∏ i, μ i (x i)

/-- Exact factorization of finite product expectations. -/
theorem finiteProduct_expectation_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) :
    (∑ x : ∀ i, Ω i, (∏ i, f i (x i)) * finiteProductMass μ x) =
      ∏ i, ∑ y : Ω i, f i y * μ i y := by
  unfold finiteProductMass
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => f i y * μ i y)).symm

/-- Each coordinate has exactly its original finite law. -/
theorem finiteProduct_expectation_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) (hμ : ∀ i, ∑ y : Ω i, μ i y = 1) (i : ι) :
    (∑ x : ∀ i, Ω i, f i (x i) * finiteProductMass μ x) =
      ∑ y : Ω i, f i y * μ i y := by
  classical
  let g : ∀ j, Ω j → ℝ := fun j y => if j = i then f j y else 1
  have hprod (x : ∀ j, Ω j) : (∏ j, g j (x j)) = f i (x i) := by
    simp [g]
  calc
    _ = ∑ x : ∀ j, Ω j, (∏ j, g j (x j)) * finiteProductMass μ x := by
      simp_rw [hprod]
    _ = ∏ j, ∑ y : Ω j, g j y * μ j y := finiteProduct_expectation_product μ g
    _ = ∏ j, if j = i then (∑ y : Ω j, f j y * μ j y) else 1 := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · simp [g, hj]
      · simp [g, hj, hμ]
    _ = _ := by simp

/-- Distinct centered coordinates are orthogonal under the actual product
mass. This conclusion is not a covariance assumption. -/
theorem finiteProduct_centered_cross {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) (hf : ∀ i, ∑ y : Ω i, f i y * μ i y = 0)
    {i j : ι} (hij : i ≠ j) :
    (∑ x : ∀ k, Ω k, (f i (x i) * f j (x j)) * finiteProductMass μ x) = 0 := by
  classical
  let g : ∀ k, Ω k → ℝ := fun k y =>
    (if k = i then f k y else 1) * (if k = j then f k y else 1)
  have hprod (x : ∀ k, Ω k) : (∏ k, g k (x k)) = f i (x i) * f j (x j) := by
    dsimp only [g]
    rw [Finset.prod_mul_distrib]
    simp
  calc
    _ = ∑ x : ∀ k, Ω k, (∏ k, g k (x k)) * finiteProductMass μ x := by
      simp_rw [hprod]
    _ = ∏ k, ∑ y : Ω k, g k y * μ k y := finiteProduct_expectation_product μ g
    _ = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simpa [g, hij] using hf i

/-- The full centered second moment is the sum of the individual second
moments in a finite product law. -/
theorem finiteProduct_centered_secondMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) (hμ : ∀ i, ∑ y : Ω i, μ i y = 1)
    (hf : ∀ i, ∑ y : Ω i, f i y * μ i y = 0) :
    (∑ x : ∀ i, Ω i, (∑ i, f i (x i)) ^ 2 * finiteProductMass μ x) =
      ∑ i, ∑ y : Ω i, (f i y) ^ 2 * μ i y := by
  classical
  calc
    _ = ∑ x : ∀ i, Ω i, ∑ i, ∑ j,
        (f i (x i) * f j (x j)) * finiteProductMass μ x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_two, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ j, ∑ x : ∀ k, Ω k,
        (f i (x i) * f j (x j)) * finiteProductMass μ x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ y : Ω i, (f i y) ^ 2 * μ i y := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · have hi := finiteProduct_expectation_coordinate μ
          (fun k y => (f k y) ^ 2) hμ i
        convert hi using 1
        apply Finset.sum_congr rfl
        intro x _
        ring
      · intro j _ hij
        exact finiteProduct_centered_cross μ f hf (Ne.symm hij)
      · simp

/-- Exact variance of the average of mean-one coordinates in the finite
product model. The only mixed-moment input is the proved product identity. -/
theorem finiteProduct_average_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) (hμ : ∀ i, ∑ y : Ω i, μ i y = 1)
    (hf : ∀ i, ∑ y : Ω i, f i y * μ i y = 1)
    (hcard : 0 < Fintype.card ι) :
    (∑ x : ∀ i, Ω i, ((∑ i, f i (x i)) / Fintype.card ι - 1) ^ 2 *
      finiteProductMass μ x) =
      (∑ i, ((∑ y : Ω i, (f i y) ^ 2 * μ i y) - 1)) / (Fintype.card ι : ℝ) ^ 2 := by
  classical
  let g : ∀ i, Ω i → ℝ := fun i y => f i y - 1
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  have hg (i : ι) : ∑ y : Ω i, g i y * μ i y = 0 := by
    simp only [g, sub_mul, one_mul, Finset.sum_sub_distrib, hf, hμ, sub_self]
  have hsecond (i : ι) : (∑ y : Ω i, (g i y) ^ 2 * μ i y) =
      (∑ y : Ω i, (f i y) ^ 2 * μ i y) - 1 := by
    calc
      _ = ∑ y : Ω i, ((f i y) ^ 2 * μ i y - 2 * (f i y * μ i y) + μ i y) := by
        apply Finset.sum_congr rfl
        intro y _
        dsimp only [g]
        ring
      _ = (∑ y : Ω i, (f i y) ^ 2 * μ i y) -
          2 * (∑ y : Ω i, f i y * μ i y) + (∑ y : Ω i, μ i y) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by rw [hf, hμ]; ring
  have hpoint (x : ∀ i, Ω i) :
      (∑ i, f i (x i)) / Fintype.card ι - 1 = (∑ i, g i (x i)) / Fintype.card ι := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    field_simp
  calc
    _ = (∑ x : ∀ i, Ω i, (∑ i, g i (x i)) ^ 2 * finiteProductMass μ x) /
        (Fintype.card ι : ℝ) ^ 2 := by
      simp_rw [hpoint]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [div_pow]
      ring
    _ = _ := by rw [finiteProduct_centered_secondMoment μ g hμ hg]; simp_rw [hsecond]

/-- Uniform second moments give the `C/b` decay in (2.8). -/
theorem finiteProduct_average_variance_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)]
    (μ f : ∀ i, Ω i → ℝ) (hμ : ∀ i, ∑ y : Ω i, μ i y = 1)
    (hf : ∀ i, ∑ y : Ω i, f i y * μ i y = 1)
    (hcard : 0 < Fintype.card ι) {C : ℝ}
    (hsecond : ∀ i, ∑ y : Ω i, (f i y) ^ 2 * μ i y ≤ C) :
    (∑ x : ∀ i, Ω i, ((∑ i, f i (x i)) / Fintype.card ι - 1) ^ 2 *
      finiteProductMass μ x) ≤ C / Fintype.card ι := by
  classical
  rw [finiteProduct_average_variance μ f hμ hf hcard]
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard)
  calc
    _ ≤ (∑ _i : ι, C) / (Fintype.card ι : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      linarith [hsecond i]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

/-- The exact model expectation `E Z_b` from (2.8). Each array is sampled
independently from its own actual finite Bernoulli mask space. -/
noncomputable def independentArraysVariance {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ) : ℝ :=
  ∑ A : ∀ j, ArrayMasks (P j),
    ((∑ j, independentArrayWeight (P j) (V j) (A j) /
      independentArrayMean (P j) (V j)) / Fintype.card J - 1) ^ 2 *
    finiteProductMass (fun j => independentArrayMass (P j)) A

/-- Normalizing by the actual nonzero mean gives mean exactly one. -/
theorem independentArray_normalized_mean {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (V : I → ℝ) (hm : independentArrayMean P V ≠ 0) :
    (∑ A : ArrayMasks P, (independentArrayWeight P V A / independentArrayMean P V) *
      independentArrayMass P A) = 1 := by
  calc
    _ = independentArrayMean P V / independentArrayMean P V := by
      unfold independentArrayMean
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro A _
      ring
    _ = 1 := div_self hm

/-- The normalized second moment has its exact expected denominator. -/
theorem independentArray_normalized_secondMoment {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → Finset ℕ) (V : I → ℝ) :
    (∑ A : ArrayMasks P, (independentArrayWeight P V A / independentArrayMean P V) ^ 2 *
      independentArrayMass P A) =
      independentArraySecondMoment P V / (independentArrayMean P V) ^ 2 := by
  unfold independentArraySecondMoment
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A _
  rw [div_pow]
  ring

/-- The exact equality in (2.8), expressed using actual first and second
moments rather than a separate variance primitive. -/
theorem independentArraysVariance_eq {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ)
    (hcard : 0 < Fintype.card J)
    (hm : ∀ j, independentArrayMean (P j) (V j) ≠ 0) :
    independentArraysVariance P V =
      (∑ j, (independentArraySecondMoment (P j) (V j) /
        (independentArrayMean (P j) (V j)) ^ 2 - 1)) / (Fintype.card J : ℝ) ^ 2 := by
  unfold independentArraysVariance
  rw [finiteProduct_average_variance
    (fun j => independentArrayMass (P j))
    (fun j A => independentArrayWeight (P j) (V j) A / independentArrayMean (P j) (V j))
    (fun j => independentArrayMass_sum (P j))
    (fun j => independentArray_normalized_mean (P j) (V j) (hm j)) hcard]
  simp_rw [independentArray_normalized_secondMoment]

/-- Actual marking arrays have `C/b` variance whenever their normalized
second moments are bounded by `C`. All independence identities are proved. -/
theorem independentArraysVariance_le {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ)
    (hcard : 0 < Fintype.card J)
    (hm : ∀ j, independentArrayMean (P j) (V j) ≠ 0) {C : ℝ}
    (hsecond : ∀ j, independentArraySecondMoment (P j) (V j) /
      (independentArrayMean (P j) (V j)) ^ 2 ≤ C) :
    independentArraysVariance P V ≤ C / Fintype.card J := by
  unfold independentArraysVariance
  apply finiteProduct_average_variance_le
    (fun j => independentArrayMass (P j))
    (fun j A => independentArrayWeight (P j) (V j) A / independentArrayMean (P j) (V j))
    (fun j => independentArrayMass_sum (P j))
    (fun j => independentArray_normalized_mean (P j) (V j) (hm j)) hcard
  intro j
  rw [independentArray_normalized_secondMoment]
  exact hsecond j

/-- A common positive mean lower bound and common second-moment upper bound
supply the uniform constant in (2.8), independent of the number of arrays. -/
theorem independentArraysVariance_le_of_moment_bounds {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (P : J → I → Finset ℕ) (V : J → I → ℝ)
    (hcard : 0 < Fintype.card J) {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hmeans : ∀ j, c ≤ independentArrayMean (P j) (V j))
    (hseconds : ∀ j, independentArraySecondMoment (P j) (V j) ≤ M) :
    independentArraysVariance P V ≤ (M / c ^ 2) / Fintype.card J := by
  apply independentArraysVariance_le P V hcard
    (fun j => ne_of_gt (hc.trans_le (hmeans j)))
  intro j
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have hm2 : c ^ 2 ≤ (independentArrayMean (P j) (V j)) ^ 2 :=
    pow_le_pow_left₀ hc.le (hmeans j) 2
  calc
    _ ≤ M / (independentArrayMean (P j) (V j)) ^ 2 :=
      div_le_div_of_nonneg_right (hseconds j) (sq_nonneg _)
    _ ≤ M / c ^ 2 := div_le_div_of_nonneg_left hM hc2 hm2

end ArtinMatthews
