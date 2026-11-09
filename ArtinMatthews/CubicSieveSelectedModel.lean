module

public import ArtinMatthews.CubicSievePolynomialTail
public import ArtinMatthews.MarkedProgressionWeightedPolynomial


set_option backward.privateInPublic true
@[expose] public section

/-! Literal selected-prime residuals under a variable finite local model. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def cubicSieveSelectedModel (P S : Finset ℕ) (θ g : ℕ → ℝ) : ℝ :=
  (∏ p ∈ S, g p) * ∏ p ∈ P \ S, (1 - θ p * g p)

def cubicSieveSelectedTruncation (P S : Finset ℕ) (θ g : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∏ p ∈ S, g p) * BonferroniDensity.densityPolynomial k (P \ S) (fun p => θ p * g p)

def cubicSieveSelectedModelTangent (P S : Finset ℕ) (θ g v : ℕ → ℝ) : ℝ :=
  cubicSieveProdTangent S g v * (∏ p ∈ P \ S, (1 - θ p * g p)) +
    (∏ p ∈ S, g p) * cubicSieveProdTangent (P \ S)
      (fun p => 1 - θ p * g p) (fun p => -(θ p * v p))

def cubicSieveSelectedTruncationTangent (P S : Finset ℕ) (θ g v : ℕ → ℝ) (k : ℕ) : ℝ :=
  cubicSieveProdTangent S g v * BonferroniDensity.densityPolynomial k (P \ S) (fun p => θ p * g p) +
    (∏ p ∈ S, g p) * cubicSievePolynomialTangent k (P \ S)
      (fun p => θ p * g p) (fun p => θ p * v p)

theorem cubicSieve_selectedTruncation_eq_coefficients (P S : Finset ℕ) (θ g : ℕ → ℝ) (k : ℕ) :
    cubicSieveSelectedTruncation P S θ g k =
      ∑ i ∈ markedWeightedIndices P S k, markedWeightedCoefficient θ i * ∏ p ∈ S ∪ i.2, g p := by
  unfold cubicSieveSelectedTruncation BonferroniDensity.densityPolynomial BonferroniDensity.elementarySum
    markedWeightedIndices markedWeightedCoefficient
  rw [sum_sigma]
  simp only [mul_sum]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro T hT
  have hsub := (mem_powersetCard.mp hT).1
  have hdis : Disjoint S T := disjoint_left.mpr (fun p hpS hpT => (mem_sdiff.mp (hsub hpT)).2 hpS)
  rw [prod_union hdis, prod_mul_distrib]
  ring

theorem cubicSieve_selectedModel_hasDerivAt (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) (G : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (s : ℝ)
    (hv : ∀ p ∈ P, HasDerivAt (G p) (v p) s) :
    HasDerivAt (fun t => cubicSieveSelectedModel P S θ (fun p => G p t))
      (cubicSieveSelectedModelTangent P S θ (fun p => G p s) v) s := by
  have h1 := cubicSieve_hasDerivAt_prod S G v s (fun p hp => hv p (hS hp))
  have h2 := cubicSieve_hasDerivAt_prod (P \ S) (fun p t => 1 - θ p * G p t)
    (fun p => -(θ p * v p)) s (fun p hp => ((hv p (mem_sdiff.mp hp).1).const_mul (θ p)).const_sub 1)
  exact h1.mul h2

theorem cubicSieve_selectedTruncation_hasDerivAt (P S : Finset ℕ) (hS : S ⊆ P)
    (θ : ℕ → ℝ) (G : ℕ → ℝ → ℝ) (v : ℕ → ℝ) (s : ℝ)
    (hv : ∀ p ∈ P, HasDerivAt (G p) (v p) s) (k : ℕ) :
    HasDerivAt (fun t => cubicSieveSelectedTruncation P S θ (fun p => G p t) k)
      (cubicSieveSelectedTruncationTangent P S θ (fun p => G p s) v k) s := by
  have h1 := cubicSieve_hasDerivAt_prod S G v s (fun p hp => hv p (hS hp))
  have h2 := cubicSieve_hasDerivAt_densityPolynomial (P \ S) (fun p t => θ p * G p t)
    (fun p => θ p * v p) s (fun p hp => (hv p (mem_sdiff.mp hp).1).const_mul (θ p)) k
  exact h1.mul h2

theorem cubicSieve_selectedTruncation_tail (P S : Finset ℕ) (hS : S ⊆ P) (θ g : ℕ → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (hmass : (∑ p ∈ P, g p) ≤ M) (k : ℕ) :
    |cubicSieveSelectedTruncation P S θ g k - cubicSieveSelectedModel P S θ g| ≤
      (∏ p ∈ S, g p) * (2 * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k) := by
  have hprod : 0 ≤ ∏ p ∈ S, g p := prod_nonneg (fun p hp => hg p (hS hp))
  have hθg (p : ℕ) (hp : p ∈ P \ S) : 0 ≤ θ p * g p :=
    mul_nonneg (hθ p (mem_sdiff.mp hp).1).1 (hg p (mem_sdiff.mp hp).1)
  have hsum : (∑ p ∈ P \ S, θ p * g p) ≤ M :=
    (sum_le_sum (fun p hp => mul_le_of_le_one_left (hg p (mem_sdiff.mp hp).1)
      (hθ p (mem_sdiff.mp hp).1).2)).trans
        ((sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ => hg p hp)).trans hmass)
  unfold cubicSieveSelectedTruncation cubicSieveSelectedModel
  rw [← mul_sub, abs_mul, abs_of_nonneg hprod]
  exact mul_le_mul_of_nonneg_left (cubicSieve_densityPolynomial_tail_bound (P \ S)
    (fun p => θ p * g p) hM hθg hsum k) hprod

theorem cubicSieve_selectedTruncationTangent_tail (P S : Finset ℕ) (hS : S ⊆ P) (θ g v : ℕ → ℝ)
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (hv : ∀ p ∈ P, |v p| ≤ L * g p)
    (hmass : (∑ p ∈ P, g p) ≤ M) (k : ℕ) :
    |cubicSieveSelectedTruncationTangent P S θ g v k - cubicSieveSelectedModelTangent P S θ g v| ≤
      (∏ p ∈ S, g p) * (2 * L * ((S.card : ℝ) + 1) * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k) := by
  let R := P \ S
  let w (p : ℕ) := θ p * g p
  let w' (p : ℕ) := θ p * v p
  have hprod : 0 ≤ ∏ p ∈ S, g p := prod_nonneg (fun p hp => hg p (hS hp))
  have hw (p : ℕ) (hp : p ∈ R) : 0 ≤ w p :=
    mul_nonneg (hθ p (mem_sdiff.mp hp).1).1 (hg p (mem_sdiff.mp hp).1)
  have hw' (p : ℕ) (hp : p ∈ R) : |w' p| ≤ L * w p := by
    dsimp only [w, w']
    rw [abs_mul, abs_of_nonneg (hθ p (mem_sdiff.mp hp).1).1]
    exact (mul_le_mul_of_nonneg_left (hv p (mem_sdiff.mp hp).1)
      (hθ p (mem_sdiff.mp hp).1).1).trans_eq (by ring)
  have hsum : (∑ p ∈ R, w p) ≤ M :=
    (sum_le_sum (fun p hp => mul_le_of_le_one_left (hg p (mem_sdiff.mp hp).1)
      (hθ p (mem_sdiff.mp hp).1).2)).trans
        ((sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ => hg p hp)).trans hmass)
  have hD := cubicSieve_prodTangent_abs_le S g v (fun _ => L)
    (fun p hp => hg p (hS hp)) (fun p hp => hv p (hS hp))
  simp only [sum_const, nsmul_eq_mul] at hD
  have hV := cubicSieve_densityPolynomial_tail_bound R w hM hw hsum k
  have hT := cubicSieve_polynomialTangent_tail_bound R w w' hM hL hw hw' hsum k
  have heq : cubicSieveSelectedTruncationTangent P S θ g v k - cubicSieveSelectedModelTangent P S θ g v =
      cubicSieveProdTangent S g v * (BonferroniDensity.densityPolynomial k R w - ∏ p ∈ R, (1 - w p)) +
        (∏ p ∈ S, g p) * (cubicSievePolynomialTangent k R w w' -
          cubicSieveProdTangent R (fun p => 1 - w p) (fun p => -w' p)) := by
    unfold cubicSieveSelectedTruncationTangent cubicSieveSelectedModelTangent
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hprod]
  exact (add_le_add (mul_le_mul hD hV (abs_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left hT hprod)).trans_eq (by ring)

end ArtinMatthews
