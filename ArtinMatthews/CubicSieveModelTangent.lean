module

public import ArtinMatthews.CubicSieveCorrectionModel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite product and elementary-symmetric tangents for the signed
sieve model. The original signs are kept in the polynomial tangent. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def cubicSieveProdTangent (P : Finset ℕ) (g v : ℕ → ℝ) : ℝ :=
  ∑ p ∈ P, (∏ q ∈ P.erase p, g q) * v p

def cubicSieveElementaryTangent (P : Finset ℕ) (g v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ P.powersetCard k, cubicSieveProdTangent T g v

def cubicSievePolynomialTangent (k : ℕ) (P : Finset ℕ) (g v : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * cubicSieveElementaryTangent P g v j

theorem cubicSieve_hasDerivAt_prod (P : Finset ℕ) (G : ℕ → ℝ → ℝ)
    (v : ℕ → ℝ) (s : ℝ) (hv : ∀ p ∈ P, HasDerivAt (G p) (v p) s) :
    HasDerivAt (fun t => ∏ p ∈ P, G p t) (cubicSieveProdTangent P (fun p => G p s) v) s := by
  simpa only [cubicSieveProdTangent, smul_eq_mul] using HasDerivAt.fun_finsetProd hv

theorem cubicSieve_hasDerivAt_elementary (P : Finset ℕ) (G : ℕ → ℝ → ℝ)
    (v : ℕ → ℝ) (s : ℝ) (hv : ∀ p ∈ P, HasDerivAt (G p) (v p) s) (k : ℕ) :
    HasDerivAt (fun t => BonferroniDensity.elementarySum P (fun p => G p t) k)
      (cubicSieveElementaryTangent P (fun p => G p s) v k) s := by
  unfold BonferroniDensity.elementarySum cubicSieveElementaryTangent
  apply HasDerivAt.fun_sum
  intro T hT
  exact cubicSieve_hasDerivAt_prod T G v s (fun p hp => hv p (mem_powersetCard.mp hT |>.1 hp))

theorem cubicSieve_hasDerivAt_densityPolynomial (P : Finset ℕ) (G : ℕ → ℝ → ℝ)
    (v : ℕ → ℝ) (s : ℝ) (hv : ∀ p ∈ P, HasDerivAt (G p) (v p) s) (k : ℕ) :
    HasDerivAt (fun t => BonferroniDensity.densityPolynomial k P (fun p => G p t))
      (cubicSievePolynomialTangent k P (fun p => G p s) v) s := by
  unfold BonferroniDensity.densityPolynomial cubicSievePolynomialTangent
  apply HasDerivAt.fun_sum
  intro j _
  exact (cubicSieve_hasDerivAt_elementary P G v s hv j).const_mul _

theorem cubicSieve_prodTangent_abs_le (P : Finset ℕ) (g v L : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) (hv : ∀ p ∈ P, |v p| ≤ L p * g p) :
    |cubicSieveProdTangent P g v| ≤ (∑ p ∈ P, L p) * ∏ p ∈ P, g p := by
  unfold cubicSieveProdTangent
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [sum_mul]
  apply sum_le_sum
  intro p hp
  have hpos : 0 ≤ ∏ q ∈ P.erase p, g q := prod_nonneg (fun q hq => hg q (mem_of_mem_erase hq))
  rw [abs_mul, abs_of_nonneg hpos]
  exact (mul_le_mul_of_nonneg_left (hv p hp) hpos).trans_eq (by
    rw [← prod_erase_mul P g hp]
    ring)

theorem cubicSieve_elementaryTangent_abs_le (P : Finset ℕ) (g v : ℕ → ℝ) (L : ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p) (hv : ∀ p ∈ P, |v p| ≤ L * g p) (k : ℕ) :
    |cubicSieveElementaryTangent P g v k| ≤ (k : ℝ) * L * BonferroniDensity.elementarySum P g k := by
  unfold cubicSieveElementaryTangent BonferroniDensity.elementarySum
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro T hT
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hT
  simpa only [sum_const, nsmul_eq_mul, hcard] using
    cubicSieve_prodTangent_abs_le T g v (fun _ => L)
      (fun p hp => hg p (hsub hp)) (fun p hp => hv p (hsub hp))

end ArtinMatthews
