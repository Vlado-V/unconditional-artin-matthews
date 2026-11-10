module

public import ArtinMatthews.MarkedEstimateModelBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The full independent marked-array model

The sample space records a subset of each finite prime band. Its mass is
the product of the band's Bernoulli masses. For disjoint prime bands this
is exactly the independent divisor model in Section 2 of the manuscript.
The first and second moments below are finite sums, not asymptotic inputs.
-/

namespace ArtinMatthews

/-- The masks recording the prime divisors from each of the bands. -/
abbrev ArrayMasks {ι : Type*} (P : ι → Finset ℕ) := ∀ i, ↥(P i).powerset

noncomputable def independentArrayWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) (A : ArrayMasks P) : ℝ :=
  ∏ i, halfDampedCount (A i).val.card / V i

noncomputable def independentArrayMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (A : ArrayMasks P) : ℝ :=
  ∏ i, bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) (A i).val

noncomputable def independentArrayMean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) : ℝ :=
  ∑ A : ArrayMasks P, independentArrayWeight P V A * independentArrayMass P A

noncomputable def independentArraySecondMoment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) : ℝ :=
  ∑ A : ArrayMasks P, (independentArrayWeight P V A) ^ 2 * independentArrayMass P A

/-- Total mass one is an exact identity on this finite product model. -/
theorem independentArrayMass_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) : ∑ A : ArrayMasks P, independentArrayMass P A = 1 := by
  unfold independentArrayMass
  rw [← Fintype.prod_sum (fun i (A : ↥(P i).powerset) =>
    bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A.val)]
  have hm (i : ι) :
      (∑ A : ↥(P i).powerset, bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A.val) = 1 := by
    rw [Finset.sum_coe_sort]
    exact bernoulliMaskMass_sum _ _
  simp_rw [hm]
  simp

/-- Factorization of the first moment by independence, proved by finite
product/sum distributivity. -/
theorem independentArrayMean_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) :
    independentArrayMean P V =
      ∏ i, bernoulliBandMean (P i) (fun p => 1 / (p : ℝ)) (V i) := by
  unfold independentArrayMean independentArrayWeight independentArrayMass
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (A : ↥(P i).powerset) =>
    halfDampedCount A.val.card / V i * bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A.val)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.sum_coe_sort (P i).powerset (fun A =>
    halfDampedCount A.card / V i * bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A)]
  unfold bernoulliBandMean
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A _
  ring

/-- Factorization of the full second moment, including repeated arrays. -/
theorem independentArraySecondMoment_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (V : ι → ℝ) :
    independentArraySecondMoment P V =
      ∏ i, bernoulliBandSecondMoment (P i) (fun p => 1 / (p : ℝ)) (V i) := by
  unfold independentArraySecondMoment independentArrayWeight independentArrayMass
  simp_rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (A : ↥(P i).powerset) =>
    (halfDampedCount A.val.card / V i) ^ 2 * bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A.val)]
  apply Finset.prod_congr rfl
  intro i _
  rw [Finset.sum_coe_sort (P i).powerset (fun A =>
    (halfDampedCount A.card / V i) ^ 2 * bernoulliMaskMass (P i) (fun p => 1 / (p : ℝ)) A)]
  rfl

/-- Uniform constants for both moments, depending only on the number of
bands and their common positive lower mass bound. -/
theorem independentArray_moment_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset ℕ) (hP : ∀ i p, p ∈ P i → p.Prime)
    {v : ℝ} (hv : 0 < v)
    (hlo : ∀ i, v ≤ bandReciprocalMass (P i))
    (hhi : ∀ i, bandReciprocalMass (P i) ≤ 1) :
    (1 / 2 : ℝ) ^ Fintype.card ι ≤ independentArrayMean P (fun i => bandReciprocalMass (P i)) ∧
    independentArrayMean P (fun i => bandReciprocalMass (P i)) ≤ (1 / v) ^ Fintype.card ι ∧
    independentArraySecondMoment P (fun i => bandReciprocalMass (P i)) ≤
      ((1 / v) ^ 2) ^ Fintype.card ι := by
  have hb (i : ι) := primeBand_model_bounds (P i) (hP i) hv (hlo i) (hhi i)
  rw [independentArrayMean_eq, independentArraySecondMoment_eq]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun _ : ι => (1 / 2 : ℝ)) (g := fun i =>
          bernoulliBandMean (P i) (fun p => 1 / (p : ℝ)) (bandReciprocalMass (P i)))
        (fun _ _ => by positivity) (fun i _ => (hb i).1))
  · simpa only [Finset.prod_const, Finset.card_univ] using
      (Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i => bernoulliBandMean (P i) (fun p => 1 / (p : ℝ)) (bandReciprocalMass (P i)))
        (g := fun _ : ι => 1 / v)
        (fun i _ => (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (hb i).1)
        (fun i _ => (hb i).2.1))
  · have hsecond := Finset.prod_le_prod₀ (s := Finset.univ)
        (f := fun i => bernoulliBandSecondMoment (P i) (fun p => 1 / (p : ℝ)) (bandReciprocalMass (P i)))
        (g := fun _ : ι => (1 / v) ^ 2)
    have hn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤
        bernoulliBandSecondMoment (P i) (fun p => 1 / (p : ℝ)) (bandReciprocalMass (P i)) := by
      intro i _
      unfold bernoulliBandSecondMoment
      apply Finset.sum_nonneg
      intro A hA
      exact mul_nonneg (sq_nonneg _) (bernoulliMaskMass_nonneg _ _
        (primeReciprocal_probabilities (P i) (hP i)) (Finset.mem_powerset.mp hA))
    simpa only [Finset.prod_const, Finset.card_univ] using hsecond hn (fun i _ => (hb i).2.2)

end ArtinMatthews
