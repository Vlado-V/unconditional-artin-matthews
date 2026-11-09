module

public import ArtinMatthews.DivisorWeights
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-!
# Explicit bounds for the independent divisor model

The exact finite Bernoulli formula implies a uniform lower bound without
any probabilistic approximation. If the reciprocal mass `V` of a band is
at most one, its normalized marked mean is at least one half. This applies
to the manuscript's bands once their masses tend to `log 2`.
-/

namespace ArtinMatthews

/-- Elementary finite product lower bound for probabilities in `[0,1]`. -/
theorem one_sub_sum_le_product {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1) :
    1 - (∑ i ∈ P, r i) ≤ ∏ i ∈ P, (1 - r i) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
    have har := hr a (Finset.mem_insert_self _ _)
    have hP : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1 :=
      fun i hi => hr i (Finset.mem_insert_of_mem hi)
    have hprod := mul_le_mul_of_nonneg_left (ih hP) (sub_nonneg.mpr har.2)
    have hsum : 0 ≤ ∑ i ∈ P, r i := Finset.sum_nonneg (fun i hi => (hP i hi).1)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg har.1 hsum]

/-- Explicit lower bound for the one-band marked mean. The normalizer is
the actual sum of the Bernoulli hit probabilities. -/
theorem bernoulliBandMean_lower {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    (hV : 0 < ∑ i ∈ P, r i) :
    1 - (∑ i ∈ P, r i) / 2 ≤ bernoulliBandMean P r (∑ i ∈ P, r i) := by
  rw [bernoulliBandMean_eq]
  apply (le_div_iff₀ hV).mpr
  have hp (i : ι) :
      1 - (∑ j ∈ P, r j) / 2 ≤
        ∏ j ∈ P.erase i, (1 - r j + (1 / 2 : ℝ) * r j) := by
    have he := one_sub_sum_le_product (P.erase i) (fun j => r j / 2) (by
      intro j hj
      obtain ⟨hlo, hhi⟩ := hr j (Finset.mem_of_mem_erase hj)
      constructor <;> linarith)
    have hs : (∑ j ∈ P.erase i, r j / 2) ≤ (∑ j ∈ P, r j) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun j hj _ => div_nonneg (hr j hj).1 (by norm_num))
    have heq : (∏ j ∈ P.erase i, (1 - r j / 2)) =
        ∏ j ∈ P.erase i, (1 - r j + (1 / 2 : ℝ) * r j) := by
      apply Finset.prod_congr rfl
      intro j _
      ring
    rw [heq] at he
    linarith
  calc
    (1 - (∑ i ∈ P, r i) / 2) * ∑ i ∈ P, r i =
        ∑ i ∈ P, r i * (1 - (∑ j ∈ P, r j) / 2) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hp i) (hr i hi).1)

/-- The lower constant is independent of the locations of the band primes. -/
theorem bernoulliBandMean_ge_half {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    (hV : 0 < ∑ i ∈ P, r i) (hVone : (∑ i ∈ P, r i) ≤ 1) :
    (1 / 2 : ℝ) ≤ bernoulliBandMean P r (∑ i ∈ P, r i) := by
  have h := bernoulliBandMean_lower P r hr hV
  linarith

/-- Finite one-band second moment in the independent divisor model. -/
noncomputable def bernoulliBandSecondMoment {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (V : ℝ) : ℝ :=
  ∑ A ∈ P.powerset, (halfDampedCount A.card / V) ^ 2 * bernoulliMaskMass P r A

theorem bernoulliBandSecondMoment_le {ι : Type*} [DecidableEq ι]
    (P : Finset ι) (r : ι → ℝ) (hr : ∀ i ∈ P, 0 ≤ r i ∧ r i ≤ 1)
    {V : ℝ} (hV : 0 < V) :
    bernoulliBandSecondMoment P r V ≤ (1 / V) ^ 2 := by
  unfold bernoulliBandSecondMoment
  calc
    _ ≤ ∑ A ∈ P.powerset, (1 / V) ^ 2 * bernoulliMaskMass P r A := by
      apply Finset.sum_le_sum
      intro A hA
      apply mul_le_mul_of_nonneg_right _
        (bernoulliMaskMass_nonneg P r hr (Finset.mem_powerset.mp hA))
      apply pow_le_pow_left₀ (div_nonneg (halfDampedCount_nonneg _) hV.le)
      exact div_le_div_of_nonneg_right (halfDampedCount_le_one _) hV.le
    _ = _ := by rw [← Finset.mul_sum, bernoulliMaskMass_sum, mul_one]

/-- Prime divisor probabilities satisfy the Bernoulli hypotheses. -/
theorem primeReciprocal_probabilities (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∀ p ∈ P, 0 ≤ (1 : ℝ) / p ∧ (1 : ℝ) / p ≤ 1 := by
  intro p hp
  have hpone : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_le
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0 : ℝ) < p)).mpr hpone

/-- Explicit simultaneous first- and second-moment bounds for an actual
prime band, once its reciprocal mass lies in the fixed interval `[v,1]`. -/
theorem primeBand_model_bounds (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {v : ℝ} (hv : 0 < v) (hlo : v ≤ bandReciprocalMass P)
    (hhi : bandReciprocalMass P ≤ 1) :
    (1 / 2 : ℝ) ≤ bernoulliBandMean P (fun p => 1 / (p : ℝ)) (bandReciprocalMass P) ∧
    bernoulliBandMean P (fun p => 1 / (p : ℝ)) (bandReciprocalMass P) ≤ 1 / v ∧
    bernoulliBandSecondMoment P (fun p => 1 / (p : ℝ)) (bandReciprocalMass P) ≤ (1 / v) ^ 2 := by
  have hmass : 0 < bandReciprocalMass P := hv.trans_le hlo
  have hprob := primeReciprocal_probabilities P hP
  have hinv : 1 / bandReciprocalMass P ≤ 1 / v := one_div_le_one_div_of_le hv hlo
  refine ⟨bernoulliBandMean_ge_half P _ hprob hmass hhi, ?_, ?_⟩
  · exact (bernoulliBandMean_le P _ hprob hmass).trans hinv
  · exact (bernoulliBandSecondMoment_le P _ hprob hmass).trans
      (pow_le_pow_left₀ (by positivity) hinv 2)

end ArtinMatthews
