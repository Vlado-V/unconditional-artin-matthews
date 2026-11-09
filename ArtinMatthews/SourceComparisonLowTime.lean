module

public import ArtinMatthews.SourceComparisonCenteredPhase
public import ArtinMatthews.SourceComparisonDivisorL2
public import ArtinMatthews.SourceComparisonLiteralMarks
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Analysis.Real.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The quantitative low-time endpoint uses the centered divisor model and
its squared approximation error on the actual interval. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

def sourceComparisonDivisorErrorBudget (P : G → Finset ℕ) (t : G → ℕ) (j : ℕ) : ℝ :=
  (sourceComparisonMarkFactorialMass P t) ^ 2 / (2 : ℝ) ^ (j + 1) *
    Real.exp ((8 * Real.exp 2 - 1) * ∑ p ∈ univ.biUnion P, 1 / (p : ℝ))

private theorem comparison_divisor_coprime (P : G → Finset ℕ) (t : G → ℕ) (j : ℕ)
    {i : SourceComparisonDivisorIndex t} (hi : i ∈ sourceComparisonDivisorIndices P t j)
    (k : ℕ) (hk : ∀ p ∈ univ.biUnion P, p.Coprime k) :
    (sourceComparisonDivisor i).Coprime k := by
  unfold sourceComparisonDivisor markedWeightedDivisor
  exact Nat.Coprime.prod_left (fun p hp => hk p (sourceComparisonDivisor_prime_set_subset P t j hi hp))

private theorem comparisonL2_replacement {H H₀ B : ℕ → ℂ} (N : ℕ) {M E : ℝ}
    (hM : 0 ≤ M)
    (hB : ∀ n ∈ Ioc 0 N, ‖B n‖ ≤ M)
    (hH : (∑ n ∈ Ioc 0 N, ‖H n - H₀ n‖ ^ 2) ≤ (N : ℝ) * E) :
    ‖(∑ n ∈ Ioc 0 N, B n * H n) - ∑ n ∈ Ioc 0 N, B n * H₀ n‖ ≤
      M * (N : ℝ) * Real.sqrt E := by
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Ioc 0 N)
    (fun _ => (1 : ℝ)) (fun n => ‖H n - H₀ n‖)
  have hC : (∑ n ∈ Ioc 0 N, ‖H n - H₀ n‖) ≤
      Real.sqrt (N : ℝ) * Real.sqrt (∑ n ∈ Ioc 0 N, ‖H n - H₀ n‖ ^ 2) := by
    simpa using hCS
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, M * ‖H n - H₀ n‖ := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB n hn) (norm_nonneg _)
    _ ≤ M * (Real.sqrt (N : ℝ) * Real.sqrt ((N : ℝ) * E)) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ hM
      exact hC.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH) (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul (Nat.cast_nonneg N), ← mul_assoc (Real.sqrt (N : ℝ)),
        Real.mul_self_sqrt (Nat.cast_nonneg N), mul_assoc]

theorem sourceComparisonLowTime_bound (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hP : ∀ p ∈ univ.biUnion P, p.Prime) (hV : ∀ g, 0 < bandReciprocalMass (P g))
    (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1) (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) (j : ℕ)
    {Z : ℝ} (hZ : 1 ≤ Z) (hpZ : ∀ p ∈ univ.biUnion P, (p : ℝ) ≤ Z)
    (L : Finset ℕ) (hL : ∀ p ∈ L, p.Prime) (hsep : Disjoint L (univ.biUnion P))
    (k : ℕ) [NeZero k] (hk : ∀ p ∈ univ.biUnion P ∪ L, p.Coprime k)
    (A : ZMod k → ℂ) (hA : ∀ a, ‖A a‖ ≤ 1)
    (f : ℝ → ℂ) {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hf : Differentiable ℝ f) (hderiv : Continuous (deriv f)) (hfT : f T = 0) (hf0 : f 0 = 0)
    (hF : ∀ n ∈ Ioc 0 ⌊T⌋₊, ‖f n‖ ≤ M)
    (hC : ∀ n ∈ Ioc 0 ⌊T⌋₊, ‖sourceComparisonLongCenter L n‖ ≤ 1) :
    ‖∑ n ∈ Ioc 0 ⌊T⌋₊, A (n : ZMod k) * f n * sourceComparisonLongCenter L n *
      sourceComparisonMarkWeight P t q b n‖ ≤
      M * (⌊T⌋₊ : ℝ) * Real.sqrt (sourceComparisonDivisorErrorBudget P t j) +
        (((L.card : ℝ) + sourceComparisonLongReciprocal L) *
          ((3 * (k : ℝ)) * ∫ u in Set.Ioc 0 T, ‖deriv f u‖)) *
          (Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) * Z ^ ((∑ g, t g) + j)) := by
  classical
  let B (n : ℕ) := A (n : ZMod k) * f n * sourceComparisonLongCenter L n
  let I := Ioc 0 ⌊T⌋₊
  let E := sourceComparisonDivisorErrorBudget P t j
  let M₀ := ((L.card : ℝ) + sourceComparisonLongReciprocal L) *
    ((3 * (k : ℝ)) * ∫ u in Set.Ioc 0 T, ‖deriv f u‖)
  have hM₀ : 0 ≤ M₀ := by
    unfold M₀ sourceComparisonLongReciprocal
    positivity
  have hB (n : ℕ) (hn : n ∈ I) : ‖B n‖ ≤ M := by
    unfold B
    rw [norm_mul, norm_mul]
    calc
      _ ≤ (1 * M) * 1 := mul_le_mul (mul_le_mul (hA _) (hF n hn) (norm_nonneg _) zero_le_one)
        (hC n hn) (norm_nonneg _) (by positivity)
      _ = M := by ring
  have hL2 : (∑ n ∈ I, ‖sourceComparisonMarkWeight P t q b n -
      sourceComparisonDivisorModel P t q b j n‖ ^ 2) ≤ (⌊T⌋₊ : ℝ) * E := by
    simpa only [E, sourceComparisonDivisorErrorBudget, mul_div_assoc, mul_assoc] using
      sourceComparisonDivisorModel_l2_error P t q hdis hq hV hP b hb j ⌊T⌋₊
  have hr := comparisonL2_replacement (H := sourceComparisonMarkWeight P t q b)
    (H₀ := sourceComparisonDivisorModel P t q b j) (B := B) ⌊T⌋₊ hM hB hL2
  have hm : ‖∑ n ∈ I, B n * sourceComparisonDivisorModel P t q b j n‖ ≤
      M₀ * (Real.exp (∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) * Z ^ ((∑ g, t g) + j)) := by
    have ha := sourceComparisonCenteredDivisorSum_bound L (sourceComparisonDivisorIndices P t j)
      sourceComparisonDivisor (sourceComparisonDivisorCoefficient P t q b) k A hA
      (fun i hi => ⟨sourceComparisonDivisor_pos P t j hP hi,
        comparison_divisor_coprime P t j hi k (fun p hp => hk p (mem_union_left _ hp))⟩)
      (fun p hp => ⟨(hL p hp).pos, hk p (mem_union_right _ hp)⟩)
      (fun i hi p hp => (comparison_divisor_coprime P t j hi p (fun r hr =>
        (Nat.coprime_primes (hP r hr) (hL p hp)).mpr
          (fun he => disjoint_left.mp hsep hp (he ▸ hr)))).symm)
      f hT hf hderiv hfT
    have he : (∑ n ∈ Icc 0 ⌊T⌋₊, B n * sourceComparisonDivisorModel P t q b j n) =
        ∑ n ∈ I, B n * sourceComparisonDivisorModel P t q b j n := by
      rw [Icc_eq_cons_Ioc (Nat.zero_le _), sum_cons]
      simp [B, hf0, I]
    change ‖∑ n ∈ Icc 0 ⌊T⌋₊, B n * sourceComparisonDivisorModel P t q b j n‖ ≤
      M₀ * _ at ha
    rw [he] at ha
    exact ha.trans (mul_le_mul_of_nonneg_left
      (sourceComparisonDivisorCoefficient_mass_bound P t q j hdis hV hq hP b hb hZ hpZ) hM₀)
  change ‖∑ n ∈ I, B n * sourceComparisonMarkWeight P t q b n‖ ≤ _
  let a := ∑ n ∈ I, B n * sourceComparisonMarkWeight P t q b n
  let b₀ := ∑ n ∈ I, B n * sourceComparisonDivisorModel P t q b j n
  calc
    ‖a‖ = ‖(a - b₀) + b₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖a - b₀‖ + ‖b₀‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hr hm

end
end ArtinMatthews
