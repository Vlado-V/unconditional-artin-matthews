module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import ArtinMatthews.AdditiveCuspBound
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Discrete partial summation transfers the actual uniform additive cusp
bound to smoothly weighted coefficient polynomials. The variation is explicit. -/

noncomputable section
open Complex UpperHalfPlane Finset AddCircle
open scoped BigOperators

namespace ArtinMatthews

/-- The precise sampled variation appearing in finite partial summation. -/
def sampledVariation (N : ℕ) (v : ℕ → ℂ) : ℝ :=
  ‖v N‖ + ∑ n ∈ range N, ‖v n - v (n + 1)‖

/-- Finite Abel summation with all endpoint terms included. -/
theorem shifted_abel_identity (c v : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, c n * v n) =
      (∑ n ∈ range N, c n) * v N +
        ∑ n ∈ range N, (∑ k ∈ range (n + 1), c k) * (v n - v (n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [sum_range_succ] at ih ⊢
    rw [ih]
    ring

/-- Weighted sums lose only sampled variation, not the number of coefficients. -/
theorem shifted_weighted_sum_le (c v : ℕ → ℂ) (N : ℕ) (B : ℝ) (_hB : 0 ≤ B)
    (hc : ∀ n ≤ N, ‖∑ k ∈ range n, c k‖ ≤ B) :
    ‖∑ n ∈ range N, c n * v n‖ ≤ B * sampledVariation N v := by
  rw [shifted_abel_identity]
  calc
    _ ≤ ‖(∑ n ∈ range N, c n) * v N‖ +
        ∑ n ∈ range N, ‖(∑ k ∈ range (n + 1), c k) * (v n - v (n + 1))‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ B * ‖v N‖ + ∑ n ∈ range N, B * ‖v n - v (n + 1)‖ := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc N le_rfl) (norm_nonneg _)
      · apply sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hc (n + 1) (by simpa using mem_range.mp hn)) (norm_nonneg _)
    _ = _ := by rw [← mul_sum]; unfold sampledVariation; ring

/-- Uniformity for all prefixes of a fixed cutoff, including prefixes 0 and 1. -/
theorem weightOne_additive_prefix_bound
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ n ≤ N,
      ∀ x : AddCircle (1 : ℝ),
        ‖∑ k ∈ range n, (qExpansion 1 f).coeff k * fourier (k : ℤ) x‖ ≤
          C * Real.sqrt N * Real.log (2 * N) := by
  obtain ⟨C, hC, hb⟩ := weightOne_additive_sum_le_sqrt_mul_log f hperiod
  refine ⟨C, hC, fun N hN n hn x ↦ ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogN : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*N))
  by_cases hn2 : 2 ≤ n
  · induction x using QuotientAddGroup.induction_on with | H x =>
      have hbase := hb n hn2 x
      have hnN : (n : ℝ) ≤ N := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hlogn : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*n))
      exact hbase.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hnN) hC)
        (Real.log_le_log (by positivity) (by linarith)) hlogn (by positivity))
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · simp only [range_zero, sum_empty, norm_zero]
      positivity
    · simp only [sum_range_one, CuspFormClass.qExpansion_coeff_zero f (by norm_num) hperiod,
        zero_mul, norm_zero]
      positivity

/-- The actual additive cusp estimate with an arbitrary sampled smooth weight. -/
theorem weightOne_weighted_additive_bound
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ v : ℕ → ℂ,
      ∀ x : AddCircle (1 : ℝ),
        ‖∑ k ∈ range N, (qExpansion 1 f).coeff k * v k * fourier (k : ℤ) x‖ ≤
          C * Real.sqrt N * Real.log (2 * N) * sampledVariation N v := by
  obtain ⟨C, hC, hb⟩ := weightOne_additive_prefix_bound f hperiod
  refine ⟨C, hC, fun N hN v x ↦ ?_⟩
  have he := shifted_weighted_sum_le (fun k ↦ (qExpansion 1 f).coeff k * fourier (k : ℤ) x)
    v N (C * Real.sqrt N * Real.log (2 * N)) (by
      apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast (by omega : 1 ≤ 2*N)) (fun n hn ↦ hb N hN n hn x)
  convert he using 2
  apply sum_congr rfl
  intro k _
  ring

end ArtinMatthews
