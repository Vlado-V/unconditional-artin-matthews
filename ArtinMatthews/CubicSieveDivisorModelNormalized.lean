module

public import ArtinMatthews.CubicSieveModelTangent
public import ArtinMatthews.MarkedSieveMertens


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Section 7.1 model and its derivative with fixed Euler
normalization at the point of evaluation. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

def cubicSieveDivisorCorrectionModel (z : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  cubicSieveCorrectionModel z m (fun p => cubicSievePrimeDivisorModel s p)

def cubicSieveDivisorBlockEuler (z : ℝ) (j : ℕ) : ℝ :=
  ∏ p ∈ cubicSieveBlock z j, (1 - cubicSievePrimeDivisorModel 1 p)

def cubicSieveDivisorBlockUpperRatio (z : ℝ) (m j : ℕ) (s : ℝ) : ℝ :=
  BonferroniDensity.densityPolynomial (2 * cubicSieveOrder m j) (cubicSieveBlock z j)
    (fun p => cubicSievePrimeDivisorModel s p) / cubicSieveDivisorBlockEuler z j

def cubicSieveDivisorBlockOverflowRatio (z : ℝ) (m j : ℕ) (s : ℝ) : ℝ :=
  BonferroniDensity.elementarySum (cubicSieveBlock z j) (fun p => cubicSievePrimeDivisorModel s p)
    (2 * cubicSieveOrder m j + 1) / cubicSieveDivisorBlockEuler z j

def cubicSieveDivisorBlockUpperTangent (z : ℝ) (m j : ℕ) : ℝ :=
  cubicSievePolynomialTangent (2 * cubicSieveOrder m j) (cubicSieveBlock z j)
    (fun p => cubicSievePrimeDivisorModel 1 p) cubicSievePrimeDivisorDensityDerivative /
      cubicSieveDivisorBlockEuler z j

def cubicSieveDivisorBlockOverflowTangent (z : ℝ) (m j : ℕ) : ℝ :=
  cubicSieveElementaryTangent (cubicSieveBlock z j) (fun p => cubicSievePrimeDivisorModel 1 p)
    cubicSievePrimeDivisorDensityDerivative (2 * cubicSieveOrder m j + 1) /
      cubicSieveDivisorBlockEuler z j

def cubicSieveDivisorModelNormalizedDerivative (z : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ cubicSieveBlockIndices z,
    (cubicSieveDivisorBlockOverflowTangent z m j *
      (∏ i ∈ (cubicSieveBlockIndices z).erase j, cubicSieveDivisorBlockUpperRatio z m i 1) +
    cubicSieveDivisorBlockOverflowRatio z m j 1 *
      cubicSieveProdTangent ((cubicSieveBlockIndices z).erase j)
        (fun i => cubicSieveDivisorBlockUpperRatio z m i 1) (cubicSieveDivisorBlockUpperTangent z m))

theorem cubicSieve_divisorBlockEuler_product (z : ℝ) :
    (∏ j ∈ cubicSieveBlockIndices z, cubicSieveDivisorBlockEuler z j) =
      markedSieveEulerProduct z ^ 2 := by
  unfold cubicSieveDivisorBlockEuler
  have hdis : ((cubicSieveBlockIndices z : Finset ℕ) : Set ℕ).PairwiseDisjoint (cubicSieveBlock z) :=
    fun _ _ _ _ hne => cubicSieveBlock_disjoint z hne
  rw [← prod_biUnion hdis, cubicSieveBlock_union z, markedSieveEulerProduct, ← prod_pow]
  apply prod_congr rfl
  intro p hp
  rw [cubicSieve_primeDivisorModel_one (Nat.prime_of_mem_primesLE hp).pos,
    cubicSieve_primeDivisorDensity_complement, one_div]

theorem cubicSieve_divisorModel_normalized_eq_blocks (z : ℝ) (m : ℕ) (s : ℝ) :
    cubicSieveDivisorCorrectionModel z m s / markedSieveEulerProduct z ^ 2 =
      ∑ j ∈ cubicSieveBlockIndices z, cubicSieveDivisorBlockOverflowRatio z m j s *
        ∏ i ∈ (cubicSieveBlockIndices z).erase j, cubicSieveDivisorBlockUpperRatio z m i s := by
  rw [cubicSieveDivisorCorrectionModel, cubicSieve_correctionModel_eq_blocks,
    ← cubicSieve_divisorBlockEuler_product z, sum_div]
  apply sum_congr rfl
  intro j hj
  unfold cubicSieveDivisorBlockOverflowRatio cubicSieveDivisorBlockUpperRatio
  rw [prod_div_distrib, ← mul_prod_erase _ _ hj]
  exact (div_mul_div_comm _ _ _ _).symm

theorem cubicSieve_divisorBlockUpperRatio_hasDerivAt_one (z : ℝ) (m j : ℕ) :
    HasDerivAt (cubicSieveDivisorBlockUpperRatio z m j) (cubicSieveDivisorBlockUpperTangent z m j) 1 := by
  have hg (p : ℕ) (hp : p ∈ cubicSieveBlock z j) :=
    cubicSieve_primeDivisorModel_hasDerivAt_one (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
  exact (cubicSieve_hasDerivAt_densityPolynomial (cubicSieveBlock z j)
    (fun p s => cubicSievePrimeDivisorModel s p) _ 1 hg _).div_const _

theorem cubicSieve_divisorBlockOverflowRatio_hasDerivAt_one (z : ℝ) (m j : ℕ) :
    HasDerivAt (cubicSieveDivisorBlockOverflowRatio z m j) (cubicSieveDivisorBlockOverflowTangent z m j) 1 := by
  have hg (p : ℕ) (hp : p ∈ cubicSieveBlock z j) :=
    cubicSieve_primeDivisorModel_hasDerivAt_one (Nat.prime_of_mem_primesLE (mem_filter.mp hp).1).pos
  exact (cubicSieve_hasDerivAt_elementary (cubicSieveBlock z j)
    (fun p s => cubicSievePrimeDivisorModel s p) _ 1 hg _).div_const _

theorem cubicSieve_divisorModel_normalized_hasDerivAt_one (z : ℝ) (m : ℕ) :
    HasDerivAt (fun s => cubicSieveDivisorCorrectionModel z m s / markedSieveEulerProduct z ^ 2)
      (cubicSieveDivisorModelNormalizedDerivative z m) 1 := by
  simp_rw [cubicSieve_divisorModel_normalized_eq_blocks]
  unfold cubicSieveDivisorModelNormalizedDerivative
  apply HasDerivAt.fun_sum
  intro j _
  exact (cubicSieve_divisorBlockOverflowRatio_hasDerivAt_one z m j).mul
    (cubicSieve_hasDerivAt_prod ((cubicSieveBlockIndices z).erase j)
      (cubicSieveDivisorBlockUpperRatio z m) (cubicSieveDivisorBlockUpperTangent z m) 1
      (fun i _ => cubicSieve_divisorBlockUpperRatio_hasDerivAt_one z m i))

theorem cubicSieve_divisorModel_deriv_one (z : ℝ) (m : ℕ) :
    deriv (cubicSieveDivisorCorrectionModel z m) 1 =
      cubicSieveDivisorModelNormalizedDerivative z m * markedSieveEulerProduct z ^ 2 := by
  have h := (cubicSieve_divisorModel_normalized_hasDerivAt_one z m).mul_const
    (markedSieveEulerProduct z ^ 2)
  simp only [div_mul_cancel₀ _ (pow_ne_zero 2 (markedSieveEulerProduct_pos z).ne')] at h
  exact h.deriv

end ArtinMatthews
