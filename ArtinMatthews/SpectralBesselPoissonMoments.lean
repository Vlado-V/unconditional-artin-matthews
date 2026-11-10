module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
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

/-! Exact Beta moments of the Poisson weight for complex-order Bessel J. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set intervalIntegral Complex
open scoped BigOperators

/-- The polynomial moment weight on the positive unit interval. -/
def spectralPoissonMoment (ν : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ n * (1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)

/-- The Jacobian cancellation in the exact square substitution. -/
theorem spectralPoisson_square_jacobian (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (2 * u : ℂ) * ((u : ℂ) ^ 2) ^ ((n : ℂ) - 1 / 2) =
      2 * (u : ℂ) ^ (2 * n) := by
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have harg : (u : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hu.le
  have hp : ((u : ℂ) ^ 2) ^ ((n : ℂ) - 1 / 2) =
      (u : ℂ) ^ ((2 : ℂ) * ((n : ℂ) - 1 / 2)) := by
    symm
    exact Complex.cpow_nat_mul' (n := 2)
      (by simp [harg, Real.pi_pos]) (by simp [harg, Real.pi_pos.le]) _
  rw [hp]
  calc
    _ = 2 * ((u : ℂ) ^ (1 : ℂ) *
        (u : ℂ) ^ ((2 : ℂ) * ((n : ℂ) - 1 / 2))) := by rw [Complex.cpow_one]; ring
    _ = 2 * (u : ℂ) ^ ((1 : ℂ) + 2 * ((n : ℂ) - 1 / 2)) := by
      rw [Complex.cpow_add _ _ hu0]
    _ = _ := by
      have he : (1 : ℂ) + 2 * ((n : ℂ) - 1 / 2) = ((2 * n : ℕ) : ℂ) := by
        push_cast
        ring
      rw [he, Complex.cpow_natCast]

/-- Square substitution evaluates the genuine even Poisson moments. -/
theorem spectralPoisson_even_moment_beta (ν : ℂ) (hν : -(1 / 2 : ℝ) < ν.re) (n : ℕ) :
    IntervalIntegrable (spectralPoissonMoment ν (2 * n)) volume 0 1 ∧
    (∫ u : ℝ in (0 : ℝ)..1, spectralPoissonMoment ν (2 * n) u) =
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (ν + 1 / 2) / 2 := by
  let g : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((n : ℂ) - 1 / 2) * (1 - (t : ℂ)) ^ (ν - 1 / 2)
  have hg : IntervalIntegrable g volume 0 1 := by
    have hleft : 0 < ((n : ℂ) + 1 / 2).re := by
      norm_num
      positivity
    have hright : 0 < (ν + 1 / 2).re := by
      norm_num
      linarith
    convert Complex.betaIntegral_convergent hleft hright using 1
    funext t
    dsimp only [g]
    congr 1 <;> ring
  have hf : ContinuousOn (fun u : ℝ => u ^ 2) (uIcc 0 1) := by fun_prop
  have hder : ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1),
      HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    intro u _
    convert (hasDerivAt_id' u).pow 2 using 1
    norm_num
  have hpos : ∀ u ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), 0 ≤ 2 * u := by
    intro u hu
    have hu0 := hu.1
    norm_num at hu0
    linarith
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := g) hf hder hpos
  have hic := (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (g := g) hf hder hpos).mpr (by simpa only [zero_pow (by decide : 2 ≠ 0), one_pow] using hg)
  have heq : EqOn (fun u : ℝ => (2 * u) • (g ∘ (fun v : ℝ => v ^ 2)) u)
      (fun u => (2 : ℂ) * spectralPoissonMoment ν (2 * n) u) (uIoo 0 1) := by
    intro u hu
    have hu0 : 0 < u := by
      have hh := hu.1
      norm_num at hh
      exact hh
    dsimp only [Function.comp_apply]
    rw [RCLike.real_smul_eq_coe_mul]
    dsimp only [g, spectralPoissonMoment]
    push_cast
    have hj := spectralPoisson_square_jacobian n hu0
    linear_combination ((1 - (u : ℂ) ^ 2) ^ (ν - 1 / 2)) * hj
  have hi2 := hic.congr_uIoo heq
  have hi : IntervalIntegrable (spectralPoissonMoment ν (2 * n)) volume 0 1 := by
    convert hi2.const_mul (1 / 2 : ℂ) using 1
    funext u
    ring
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_congr_uIoo heq, intervalIntegral.integral_const_mul] at hsub
  have hb : (∫ u : ℝ in (0 : ℝ)..1, g u) =
      Complex.betaIntegral ((n : ℂ) + 1 / 2) (ν + 1 / 2) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [g]
    congr 1 <;> ring
  simp only [zero_pow (by decide : 2 ≠ 0), one_pow] at hsub
  rw [hb] at hsub
  linear_combination (1 / 2 : ℂ) * hsub

end ArtinMatthews
