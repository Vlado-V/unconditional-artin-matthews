module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.NumberTheory.ModularForms.Bounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Reusable steps in the shifted bilinear estimate, §5

This file proves the weight-one coefficient mean-square bound from an actual cusp form,
and the finite Cauchy--Schwarz reduction to two-point correlations.  Neither the
existence of the cubic theta series nor the shifted-correlation estimate is assumed
under the name of a theorem.  The remaining Voronoi and Kloosterman estimates are
not supplied by this file.

For the theta series in the paper, the cusp form can be viewed on the kernel of its
nebentypus (for example on Γ₁(N)).  The hypotheses below require both an arithmetic
group and period one, and explicitly identify its q-expansion with the coefficients.
-/

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex UpperHalfPlane

namespace ArtinMatthews

/-- Equation (5.5), in the stronger form `O(T)`, for coefficients that are actually
identified with a weight-one cusp form of period one.  The theta-series construction
needed to instantiate `f` and `hcoeff` is a separate mathematical input. -/
theorem weightOne_sum_norm_sq_le
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (a : ℕ → ℂ) (hcoeff : ∀ n, a n = (qExpansion 1 f).coeff n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      ∑ n ∈ Finset.range T, ‖a n‖ ^ 2 ≤ C * T := by
  obtain ⟨C, hC⟩ :=
    CuspFormClass.exists_sum_range_norm_sq_qExpansion_coeff_le_of_mem_strictPeriods
      (k := 1) f (by norm_num : (0 : ℝ) < 1) hperiod
  refine ⟨max C 0, le_max_right _ _, fun T ↦ ?_⟩
  calc
    ∑ n ∈ Finset.range T, ‖a n‖ ^ 2 ≤ C * T := by
      simpa only [hcoeff, pow_one] using hC T
    _ ≤ max C 0 * T := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)

/-- Cauchy--Schwarz in the second variable, before any estimate for the kernel.
The two coefficient sequences and the kernel may all be complex. -/
theorem bilinear_cauchy
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ) (β : κ → ℂ) (K : ι → κ → ℂ) :
    ‖∑ n ∈ t, β n * ∑ m ∈ s, α m * K m n‖ ^ 2 ≤
      (∑ n ∈ t, ‖β n‖ ^ 2) *
        ∑ n ∈ t, ‖∑ m ∈ s, α m * K m n‖ ^ 2 := by
  calc
    ‖∑ n ∈ t, β n * ∑ m ∈ s, α m * K m n‖ ^ 2 ≤
        (∑ n ∈ t, ‖β n‖ * ‖∑ m ∈ s, α m * K m n‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_mul] using
        norm_sum_le t (fun n ↦ β n * ∑ m ∈ s, α m * K m n)
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq t _ _

/-- The exact correlation expansion, including the complex conjugates. -/
theorem bilinear_energy_eq_correlations
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ) (K : ι → κ → ℂ) :
    ∑ n ∈ t, ‖∑ m ∈ s, α m * K m n‖ ^ 2 =
      (∑ m₁ ∈ s, ∑ m₂ ∈ s,
        α m₁ * conj (α m₂) *
          ∑ n ∈ t, K m₁ n * conj (K m₂ n)).re := by
  have hc : ((∑ n ∈ t, ‖∑ m ∈ s, α m * K m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₁ ∈ s, ∑ m₂ ∈ s,
        α m₁ * conj (α m₂) *
          ∑ n ∈ t, K m₁ n * conj (K m₂ n) := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m₁ hm₁
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m₂ hm₂
    apply Finset.sum_congr rfl
    intro n hn
    ring
  exact congrArg Complex.re hc

/-- The same exact expansion with a real majorant in the second variable. -/
theorem weighted_bilinear_energy_eq_correlations
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ) (K : ι → κ → ℂ) (g : κ → ℝ) :
    ∑ n ∈ t, g n * ‖∑ m ∈ s, α m * K m n‖ ^ 2 =
      (∑ m₁ ∈ s, ∑ m₂ ∈ s,
        α m₁ * conj (α m₂) *
          ∑ n ∈ t, (g n : ℂ) * K m₁ n * conj (K m₂ n)).re := by
  have hc : ((∑ n ∈ t, g n * ‖∑ m ∈ s, α m * K m n‖ ^ 2 : ℝ) : ℂ) =
      ∑ m₁ ∈ s, ∑ m₂ ∈ s,
        α m₁ * conj (α m₂) *
          ∑ n ∈ t, (g n : ℂ) * K m₁ n * conj (K m₂ n) := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m₁ hm₁
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m₂ hm₂
    apply Finset.sum_congr rfl
    intro n hn
    ring
  exact congrArg Complex.re hc

/-- The precise Cauchy reduction in §5.3, allowing a nonnegative smooth majorant
on a larger interval.  Smoothness is not used until the correlation estimate, so
this algebraic step requires only the stated pointwise inequalities. -/
theorem bilinear_cauchy_with_majorant
    {ι κ : Type*} (s : Finset ι) (t u : Finset κ) (htu : t ⊆ u)
    (α : ι → ℂ) (β : κ → ℂ) (K : ι → κ → ℂ) (g : κ → ℝ)
    (hβ : ∀ n ∈ t, ‖β n‖ ≤ 1)
    (hg : ∀ n ∈ u, 0 ≤ g n) (hmajor : ∀ n ∈ t, 1 ≤ g n) :
    ‖∑ n ∈ t, β n * ∑ m ∈ s, α m * K m n‖ ^ 2 ≤
      (t.card : ℝ) * (∑ m₁ ∈ s, ∑ m₂ ∈ s,
        α m₁ * conj (α m₂) *
          ∑ n ∈ u, (g n : ℂ) * K m₁ n * conj (K m₂ n)).re := by
  have hβ₂ : ∑ n ∈ t, ‖β n‖ ^ 2 ≤ (t.card : ℝ) := by
    calc
      ∑ n ∈ t, ‖β n‖ ^ 2 ≤ ∑ _n ∈ t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hβ n hn) 2
      _ = _ := by simp
  have henergy : ∑ n ∈ t, ‖∑ m ∈ s, α m * K m n‖ ^ 2 ≤
      ∑ n ∈ u, g n * ‖∑ m ∈ s, α m * K m n‖ ^ 2 := by
    calc
      _ ≤ ∑ n ∈ t, g n * ‖∑ m ∈ s, α m * K m n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        exact le_mul_of_one_le_left (sq_nonneg _) (hmajor n hn)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg htu
        (fun n hn _ ↦ mul_nonneg (hg n hn) (sq_nonneg _))
  rw [← weighted_bilinear_energy_eq_correlations]
  exact (bilinear_cauchy s t α β K).trans
    (mul_le_mul hβ₂ henergy (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _))

/-- The reduction used in §5.3.  All cancellation remains inside the two-point
correlations; bounded coefficients cost only the size of the second interval. -/
theorem bilinear_sq_le_card_mul_correlations
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (α : ι → ℂ) (β : κ → ℂ) (K : ι → κ → ℂ)
    (hα : ∀ m ∈ s, ‖α m‖ ≤ 1) (hβ : ∀ n ∈ t, ‖β n‖ ≤ 1) :
    ‖∑ n ∈ t, β n * ∑ m ∈ s, α m * K m n‖ ^ 2 ≤
      (t.card : ℝ) * ∑ m₁ ∈ s, ∑ m₂ ∈ s,
        ‖∑ n ∈ t, K m₁ n * conj (K m₂ n)‖ := by
  have hβ₂ : ∑ n ∈ t, ‖β n‖ ^ 2 ≤ (t.card : ℝ) := by
    calc
      ∑ n ∈ t, ‖β n‖ ^ 2 ≤ ∑ _n ∈ t, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hβ n hn) 2
      _ = _ := by simp
  have henergy : ∑ n ∈ t, ‖∑ m ∈ s, α m * K m n‖ ^ 2 ≤
      ∑ m₁ ∈ s, ∑ m₂ ∈ s, ‖∑ n ∈ t, K m₁ n * conj (K m₂ n)‖ := by
    rw [bilinear_energy_eq_correlations]
    calc
      _ ≤ ‖∑ m₁ ∈ s, ∑ m₂ ∈ s,
          α m₁ * conj (α m₂) * ∑ n ∈ t, K m₁ n * conj (K m₂ n)‖ :=
        Complex.re_le_norm _
      _ ≤ ∑ m₁ ∈ s, ∑ m₂ ∈ s,
          ‖α m₁‖ * ‖α m₂‖ * ‖∑ n ∈ t, K m₁ n * conj (K m₂ n)‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro m₁ hm₁
        simpa only [norm_mul, Complex.norm_conj] using
          norm_sum_le s (fun m₂ ↦
            α m₁ * conj (α m₂) * ∑ n ∈ t, K m₁ n * conj (K m₂ n))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro m₁ hm₁
        apply Finset.sum_le_sum
        intro m₂ hm₂
        calc
          _ ≤ 1 * 1 * ‖∑ n ∈ t, K m₁ n * conj (K m₂ n)‖ := by
            gcongr
            · exact hα m₁ hm₁
            · exact hα m₂ hm₂
          _ = _ := by ring
  exact (bilinear_cauchy s t α β K).trans
    (mul_le_mul hβ₂ henergy (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _))

/-- Normalized character averaging does not increase a common squared `ℓ²` bound.
This is the last step in (5.6), after Parseval bounds each character component.
The bound has no factor equal to the number of characters. -/
theorem normalized_average_energy_le
    {ι κ : Type*} (s : Finset ι) (t : Finset κ) (hs : s.Nonempty)
    (A : ι → κ → ℂ) (C : ℝ)
    (hA : ∀ j ∈ s, ∑ r ∈ t, ‖A j r‖ ^ 2 ≤ C) :
    ∑ r ∈ t, ‖(∑ j ∈ s, A j r) / (s.card : ℂ)‖ ^ 2 ≤ C := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hpoint (r : κ) : ‖∑ j ∈ s, A j r‖ ^ 2 ≤
      (s.card : ℝ) * ∑ j ∈ s, ‖A j r‖ ^ 2 := by
    calc
      _ ≤ (∑ j ∈ s, ‖A j r‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2
      _ ≤ _ := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ ↦ (1 : ℝ))
          (fun j ↦ ‖A j r‖)
  have hsum : ∑ r ∈ t, ‖∑ j ∈ s, A j r‖ ^ 2 ≤ C * (s.card : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ r ∈ t, (s.card : ℝ) * ∑ j ∈ s, ‖A j r‖ ^ 2 :=
        Finset.sum_le_sum fun r _ ↦ hpoint r
      _ = (s.card : ℝ) * ∑ j ∈ s, ∑ r ∈ t, ‖A j r‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (s.card : ℝ) * ∑ _j ∈ s, C := by
        gcongr with j hj
        exact hA j hj
      _ = C * (s.card : ℝ) ^ 2 := by simp; ring
  simp only [norm_div, Complex.norm_natCast, div_pow, ← Finset.sum_div]
  exact (div_le_iff₀ (sq_pos_of_pos hc)).mpr hsum

end ArtinMatthews
