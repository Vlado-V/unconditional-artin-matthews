module

public import ArtinMatthews.CubicSieveRetainedProgressions
public import ArtinMatthews.CubicSieveArithmeticBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The signed retained progression sum and its actual square-root error. -/

noncomputable section
namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators ContDiff

def cubicSieveSourceProgression (d r : ℕ) (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ u ∈ Icc 1 ⌊2 * x⌋₊, Φ ((u : ℝ) / x) * cubicSieveShiftedDivisorCoefficient d r (u + 1)

def cubicSieveSourceProgressionModel (d r : ℕ) (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  if d.Coprime r then ∫ t in Set.Ioc x (3 * x),
    cubicSieveShiftedDivisorTest Φ x t * cubicSieveShiftedDivisorLogDensity d r t else 0

theorem cubicSieve_sourceProgression_error {d r : ℕ} (hd : 0 < d) (hr : Squarefree r)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    {x : ℝ} (hx : 1 ≤ x) (hlevel : (d : ℝ) ^ 2 * (r : ℝ) ^ 2 ≤ x) :
    |cubicSieveSourceProgression d r Φ x - cubicSieveSourceProgressionModel d r Φ x| ≤
      (34 * (2 : ℝ) ^ d.primeFactors.card * (3 : ℝ) ^ r.primeFactors.card *
        Real.sqrt ((3 * x) / (r : ℝ))) *
        ∫ t in Set.Ioc x (3 * x), |deriv (cubicSieveShiftedDivisorTest Φ x) t| := by
  by_cases hc : d.Coprime r
  · simpa only [cubicSieveSourceProgression, cubicSieveSourceProgressionModel, ite_eq_left hc]
      using cubicSieve_divisorSourceWeight_smooth_error hd hr hc Φ hΦ hs hx hlevel
  · have hzero : cubicSieveSourceProgression d r Φ x = 0 := by
      unfold cubicSieveSourceProgression
      apply sum_eq_zero
      intro u _
      rw [cubicSieve_shiftedDivisorCoefficient_zero_of_not_coprime hc, mul_zero]
    rw [hzero, cubicSieveSourceProgressionModel, ite_eq_right hc, sub_self, abs_zero]
    exact mul_nonneg (by positivity)
      (setIntegral_nonneg measurableSet_Ioc (fun _ _ => abs_nonneg _))

def cubicSieveRetainedProgressionModel {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (Φ : ℝ → ℝ) (z x : ℝ) (m k : ℕ) : ℝ :=
  ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S *
    ∑ t ∈ representedArrayChoices P (fun _ => 1),
      ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
        (representedArrayCoefficient V (fun _ => 1) t *
          markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
        cubicSieveSourceProgressionModel (markedWeightedDivisor (representedArraySelected t) i)
          (roughSubsetDivisor S) Φ x

theorem cubicSieve_retainedProgression_error {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2) {z x D : ℝ} (hx : 1 ≤ x)
    (m k R : ℕ) (hD : 0 ≤ D)
    (hrange : ∀ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, cubicSieveCorrectionCoeff z m S ≠ 0 →
      roughSubsetDivisor S ≤ R)
    (hd : ∀ t ∈ representedArrayChoices P (fun _ => 1),
      ∀ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
        0 < markedWeightedDivisor (representedArraySelected t) i ∧
        (markedWeightedDivisor (representedArraySelected t) i : ℝ) ≤ D)
    (hmass : (∑ t ∈ representedArrayChoices P (fun _ => 1),
      ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
        |representedArrayCoefficient V (fun _ => 1) t *
          markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i|) ≤ D)
    (hlevel : D ^ 2 * (R : ℝ) ^ 2 ≤ x) :
    |cubicSieveRetainedWeightedSum P V Φ z x m k - cubicSieveRetainedProgressionModel P V Φ z x m k| ≤
      68 * Real.sqrt (3 * x) *
        (∫ t in Set.Ioc x (3 * x), |deriv (cubicSieveShiftedDivisorTest Φ x) t|) *
        (R : ℝ) ^ 2 * D ^ 2 := by
  let A := representedArrayChoices P (fun _ => 1)
  let I (t : (j : J) → Fin 1 → ℕ) := markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k
  let c (t : (j : J) → Fin 1 → ℕ) (i : MarkedWeightedIndex) :=
    representedArrayCoefficient V (fun _ => 1) t *
      markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i
  let Q := 34 * Real.sqrt (3 * x) * ∫ t in Set.Ioc x (3 * x), |deriv (cubicSieveShiftedDivisorTest Φ x) t|
  have hQ : 0 ≤ Q := mul_nonneg (by positivity)
    (setIntegral_nonneg measurableSet_Ioc (fun _ _ => abs_nonneg _))
  rw [cubicSieve_retainedWeightedSum_eq_progressions]
  unfold cubicSieveRetainedProgressionModel
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset, |cubicSieveCorrectionCoeff z m S| *
        ((3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card * (Q * D ^ 2)) := by
      apply sum_le_sum
      intro S hS
      by_cases he : cubicSieveCorrectionCoeff z m S = 0
      · simp only [he, zero_mul, abs_zero, le_refl]
      have hp (p : ℕ) (hp : p ∈ S) := Nat.prime_of_mem_primesLE (mem_powerset.mp hS hp)
      have hr := roughSubsetDivisor_pos S hp
      have hsq := roughSubsetDivisor_squarefree S hp
      have hR := hrange S hS he
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc
        _ ≤ ∑ t ∈ A, ∑ i ∈ I t, |c t i| * ((3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card * (Q * D)) := by
          apply sum_le_sum
          intro t ht
          refine (abs_sum_le_sum_abs _ _).trans ?_
          apply sum_le_sum
          intro i hi
          have hd' := hd t ht i hi
          have h2 : (2 : ℝ) ^ (markedWeightedDivisor (representedArraySelected t) i).primeFactors.card ≤ D := by
            calc
              _ ≤ (markedWeightedDivisor (representedArraySelected t) i : ℝ) := by
                exact_mod_cast cubicSieve_two_pow_primeFactors_le hd'.1
              _ ≤ D := hd'.2
          have hlev : (markedWeightedDivisor (representedArraySelected t) i : ℝ) ^ 2 *
              (roughSubsetDivisor S : ℝ) ^ 2 ≤ x := by
            exact (mul_le_mul (pow_le_pow_left₀ (by positivity) hd'.2 2)
              (pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr hR) 2) (by positivity) (by positivity)).trans hlevel
          have hb := cubicSieve_sourceProgression_error hd'.1 hsq Φ hΦ hs hx hlev
          have hsqrt : Real.sqrt ((3 * x) / (roughSubsetDivisor S : ℝ)) ≤ Real.sqrt (3 * x) := by
            apply Real.sqrt_le_sqrt
            exact div_le_self (by positivity) (by exact_mod_cast hr : (1 : ℝ) ≤ roughSubsetDivisor S)
          rw [← mul_sub, abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact hb.trans ((mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) (by positivity))
              hsqrt (by positivity) (by positivity))
            (setIntegral_nonneg measurableSet_Ioc (fun _ _ => abs_nonneg _))).trans_eq (by dsimp only [Q]; ring))
        _ = (∑ t ∈ A, ∑ i ∈ I t, |c t i|) * ((3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card * (Q * D)) := by
          simp_rw [← sum_mul]
        _ ≤ _ := (mul_le_mul_of_nonneg_right hmass (by positivity)).trans_eq (by ring)
    _ = (∑ S ∈ (Nat.primesLE ⌊z⌋₊).powerset,
        |cubicSieveCorrectionCoeff z m S| * (3 : ℝ) ^ (roughSubsetDivisor S).primeFactors.card) * (Q * D ^ 2) := by
      simp_rw [← mul_assoc, ← sum_mul]
    _ ≤ _ := (mul_le_mul_of_nonneg_right (cubicSieve_correctionSupport_weighted_budget m R hrange)
      (mul_nonneg hQ (sq_nonneg D))).trans_eq (by dsimp only [Q]; ring)

end ArtinMatthews
