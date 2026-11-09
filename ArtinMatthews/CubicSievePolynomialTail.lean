module

public import ArtinMatthews.CubicSieveFiniteTail


set_option backward.privateInPublic true
@[expose] public section

/-! Exact total-degree truncation and its first derivative. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

theorem cubicSieve_elementary_zero_of_card_lt (P : Finset ℕ) (g : ℕ → ℝ)
    {k : ℕ} (hk : P.card < k) : BonferroniDensity.elementarySum P g k = 0 := by
  rw [BonferroniDensity.elementarySum, powersetCard_eq_empty.mpr hk, sum_empty]

theorem cubicSieve_elementaryTangent_zero_of_card_lt (P : Finset ℕ) (g v : ℕ → ℝ)
    {k : ℕ} (hk : P.card < k) : cubicSieveElementaryTangent P g v k = 0 := by
  rw [cubicSieveElementaryTangent, powersetCard_eq_empty.mpr hk, sum_empty]

theorem cubicSieve_densityPolynomial_full (P : Finset ℕ) (g : ℕ → ℝ) :
    BonferroniDensity.densityPolynomial P.card P g = ∏ p ∈ P, (1 - g p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp only [card_empty, BonferroniDensity.densityPolynomial_empty, prod_empty]
  | @insert p P hp ih =>
    rw [card_insert_of_notMem hp, BonferroniDensity.densityPolynomial_insert P.card P g hp,
      BonferroniDensity.densityPolynomial_succ,
      cubicSieve_elementary_zero_of_card_lt P g (Nat.lt_succ_self _), mul_zero, add_zero, ih,
      prod_insert hp]
    ring

theorem cubicSieve_densityPolynomial_full_tangent (P : Finset ℕ) (g v : ℕ → ℝ) :
    cubicSievePolynomialTangent P.card P g v =
      cubicSieveProdTangent P (fun p => 1 - g p) (fun p => -v p) := by
  let G (p : ℕ) (s : ℝ) := g p + s * v p
  have hd (p : ℕ) : HasDerivAt (G p) (v p) 0 := by
    simpa only [G, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const (v p)).const_add (g p)
  have h1 := cubicSieve_hasDerivAt_densityPolynomial P G v 0 (fun p _ => hd p) P.card
  have h2 := cubicSieve_hasDerivAt_prod P (fun p s => 1 - G p s) (fun p => -v p) 0
    (fun p _ => (hd p).const_sub 1)
  have he : (fun s => BonferroniDensity.densityPolynomial P.card P (fun p => G p s)) =
      fun s => ∏ p ∈ P, (1 - G p s) := funext (fun _ => cubicSieve_densityPolynomial_full P _)
  rw [he] at h1
  simpa only [G, zero_mul, add_zero] using h1.unique h2

theorem cubicSieve_densityPolynomial_tail_bound (P : Finset ℕ) (g : ℕ → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |BonferroniDensity.densityPolynomial k P g - ∏ p ∈ P, (1 - g p)| ≤
      2 * Real.exp (8 * A) * (1 / 4 : ℝ) ^ k := by
  rw [← cubicSieve_densityPolynomial_full P g]
  apply cubicSieve_truncation_tail_abs_le P.card k
    (fun j => (-1 : ℝ) ^ j * BonferroniDensity.elementarySum P g j) (by positivity)
  · intro j hj
    rw [cubicSieve_elementary_zero_of_card_lt P g hj, mul_zero]
  · intro j
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (BonferroniDensity.elementarySum_nonneg P g hg j)]
    exact (cubicSieve_elementarySum_geometric P g hA hg hsum j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) j) (by positivity))

theorem cubicSieve_polynomialTangent_tail_bound (P : Finset ℕ) (g v : ℕ → ℝ)
    {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hv : ∀ p ∈ P, |v p| ≤ L * g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |cubicSievePolynomialTangent k P g v -
      cubicSieveProdTangent P (fun p => 1 - g p) (fun p => -v p)| ≤
      2 * (L * Real.exp (8 * A)) * (1 / 4 : ℝ) ^ k := by
  rw [← cubicSieve_densityPolynomial_full_tangent P g v]
  apply cubicSieve_truncation_tail_abs_le P.card k
    (fun j => (-1 : ℝ) ^ j * cubicSieveElementaryTangent P g v j) (by positivity)
  · intro j hj
    rw [cubicSieve_elementaryTangent_zero_of_card_lt P g v hj, mul_zero]
  · intro j
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact cubicSieve_elementaryTangent_geometric P g v hA hL hg hv hsum j

end ArtinMatthews
