module

public import ArtinMatthews.SpectralABLWindows
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

theorem spectral_norm_cos_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  have hp : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hm : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [hp, hm] at h
  have h₁ := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs z.im)
  rw [Complex.cos, norm_div]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  linarith

theorem spectralABLExceptionalWindow_strip_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A)
    (t y : ℝ) (hy : |y| ≤ 1) :
    ‖spectralABLExceptionalWindow a A ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (4 * Real.exp (4 * |Real.log a|) * ((2 * (A : ℝ) + 3) ^ 2) ^ (A + 1)) /
        (1 + t ^ 2) ^ (A - 1) := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  let B := (2 * (A : ℝ) + 3) ^ 2
  let u := 1 + t ^ 2
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hy2 : y ^ 2 ≤ 1 := by
    rcases abs_le.mp hy with ⟨hl, hr⟩
    nlinarith
  have hzsq : ‖z‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [z, Complex.normSq_apply, pow_two]
  have hden : u ≤ ‖z ^ 2 + (2 * (A : ℂ)) ^ 2‖ := by
    have hr : u ≤ (z ^ 2 + (2 * (A : ℂ)) ^ 2).re := by
      dsimp [z, u]
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      nlinarith
    exact hr.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hphase : ‖(2 * Complex.cos (2 * z * (Real.log a : ℂ))) ^ 2‖ ≤
      4 * Real.exp (4 * |Real.log a|) := by
    have him : |(2 * z * (Real.log a : ℂ)).im| ≤ 2 * |Real.log a| := by
      have he : (2 * z * (Real.log a : ℂ)).im = 2 * y * Real.log a := by
        simp [z, Complex.mul_im, Complex.mul_re]
      rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg (Real.log a)]
    have hc := (spectral_norm_cos_le_exp_abs_im (2 * z * (Real.log a : ℂ))).trans
      (Real.exp_le_exp.mpr him)
    rw [norm_pow, norm_mul]
    rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    calc
      _ ≤ (2 * Real.exp (2 * |Real.log a|)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hc (by norm_num)) 2
      _ = 4 * (Real.exp (2 * |Real.log a|) * Real.exp (2 * |Real.log a|)) := by ring
      _ = 4 * Real.exp (2 * |Real.log a| + 2 * |Real.log a|) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have hfactor (k : ℕ) (hk : k ∈ Finset.range (A + 1)) :
      ‖z ^ 2 + (((2 * k + 1 : ℕ) : ℂ) / 2) ^ 2‖ ≤ B * u := by
    have hkA : (k : ℝ) ≤ A := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hc : (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ B - 2 := by
      dsimp [B]
      push_cast
      nlinarith [sq_nonneg (k : ℝ), sq_nonneg (A : ℝ)]
    calc
      _ ≤ ‖z ^ 2‖ + ‖(((2 * k + 1 : ℕ) : ℂ) / 2) ^ 2‖ := norm_add_le _ _
      _ = t ^ 2 + y ^ 2 + (((2 * k + 1 : ℕ) : ℝ) / 2) ^ 2 := by
        rw [norm_pow, hzsq, norm_pow, norm_div]
        rw [Complex.norm_natCast, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      _ ≤ B * u := by
        dsimp [u]
        nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ B by linarith)) (sq_nonneg t)]
  have hprod : ‖∏ k ∈ Finset.range (A + 1),
      (z ^ 2 + (((2 * k + 1 : ℕ) : ℂ) / 2) ^ 2)‖ ≤ (B * u) ^ (A + 1) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _k ∈ Finset.range (A + 1), B * u :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfactor
      _ = _ := by simp
  change _ ≤ (4 * Real.exp (4 * |Real.log a|) * B ^ (A + 1)) / u ^ (A - 1)
  have hphase' : ‖2 * Complex.cos (2 * z * (Real.log a : ℂ))‖ ^ 2 ≤
      4 * Real.exp (4 * |Real.log a|) := by simpa only [norm_pow] using hphase
  unfold spectralABLExceptionalWindow
  simp only [norm_mul, norm_div, norm_pow]
  calc
    _ ≤ ((4 * Real.exp (4 * |Real.log a|)) / u ^ (2 * A)) * (B * u) ^ (A + 1) := by
      apply mul_le_mul _ hprod (norm_nonneg _) (by positivity)
      exact (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hu _)
        (pow_le_pow_left₀ hu.le hden _)).trans
          (div_le_div_of_nonneg_right (by simpa only [norm_mul] using hphase') (pow_nonneg hu.le _))
    _ = _ := by
      have hpow : 2 * A = (A + 1) + (A - 1) := by omega
      rw [hpow, pow_add, mul_pow]
      field_simp

end
end ArtinMatthews
