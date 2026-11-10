module

public import ArtinMatthews.SpectralABLCorrectedWindows
public import ArtinMatthews.SpectralABLExceptionalStrip
public import ArtinMatthews.SpectralABLRegularStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

theorem spectralABLRegularBase_strip_bound (T Δ : ℝ) (hT : 0 < T) (_hΔ : 0 < Δ)
    (t y : ℝ) (hy : |y| ≤ 1) :
    ‖spectralABLRegularBase T Δ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      2 * Real.exp (1 / Δ ^ 2) / T ^ 2 := by
  have hy2 : y ^ 2 ≤ 1 := by rcases abs_le.mp hy with ⟨hl, hr⟩; nlinarith
  have he (m : ℝ) :
      ‖Complex.exp (-((((t : ℂ) + (y : ℂ) * Complex.I - (m : ℂ)) / (Δ : ℂ)) ^ 2))‖ ≤
        Real.exp (1 / Δ ^ 2) := by
    rw [spectral_complex_gaussian_shift_norm t y m Δ]
    apply Real.exp_le_exp.mpr
    have hsq : (y / Δ) ^ 2 ≤ 1 / Δ ^ 2 := by rw [div_pow]; exact div_le_div_of_nonneg_right hy2 (sq_nonneg Δ)
    nlinarith [sq_nonneg ((t-m)/Δ)]
  have hp := he T
  have hm := he (-T)
  simp only [Complex.ofReal_neg, sub_neg_eq_add] at hm
  rw [spectralABLRegularBase, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hT.le]
  exact div_le_div_of_nonneg_right ((norm_add_le _ _).trans (by linarith)) (sq_nonneg T)

theorem spectralABLExceptionalBase_strip_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A)
    (t y : ℝ) (hy : |y| ≤ 1) :
    ‖spectralABLExceptionalBase a A ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      4 * Real.exp (4 * |Real.log a|) * ((2 * (A : ℝ) + 3) ^ 2) ^ A := by
  let z : ℂ := (t : ℂ) + (y : ℂ) * Complex.I
  let B := (2 * (A : ℝ) + 3) ^ 2
  let u := 1 + t ^ 2
  have hA' : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hy2 : y ^ 2 ≤ 1 := by rcases abs_le.mp hy with ⟨hl, hr⟩; nlinarith
  have hzsq : ‖z‖ ^ 2 = t ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [z, Complex.normSq_apply, pow_two]
  have hden : u ≤ ‖z ^ 2 + (2 * (A : ℂ)) ^ 2‖ := by
    have hr : u ≤ (z ^ 2 + (2 * (A : ℂ)) ^ 2).re := by
      dsimp [z, u]
      norm_num [pow_two, Complex.mul_re, Complex.mul_im]
      nlinarith
    exact hr.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hphase : ‖2 * Complex.cos (2 * z * (Real.log a : ℂ))‖ ^ 2 ≤
      4 * Real.exp (4 * |Real.log a|) := by
    have him : |(2 * z * (Real.log a : ℂ)).im| ≤ 2 * |Real.log a| := by
      have he : (2 * z * (Real.log a : ℂ)).im = 2 * y * Real.log a := by
        simp [z, Complex.mul_im, Complex.mul_re]
      rw [he, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [abs_nonneg (Real.log a)]
    have hb := (spectral_norm_cos_le_exp_abs_im (2 * z * (Real.log a : ℂ))).trans
      (Real.exp_le_exp.mpr him)
    rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    calc
      _ ≤ (2 * Real.exp (2 * |Real.log a|)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hb (by norm_num)) 2
      _ = 4 * (Real.exp (2 * |Real.log a|) * Real.exp (2 * |Real.log a|)) := by ring
      _ = 4 * Real.exp (2 * |Real.log a| + 2 * |Real.log a|) := by rw [Real.exp_add]
      _ = _ := by congr 2; ring
  have hfactor (k : ℕ) (hk : k ∈ Finset.range A) :
      ‖z ^ 2 + (((2 * (k + 1) + 1 : ℕ) : ℂ) / 2) ^ 2‖ ≤ B * u := by
    have hkA : (k + 1 : ℝ) ≤ A := by exact_mod_cast (Finset.mem_range.mp hk)
    have hh : (((2 * (k + 1) + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ B - 2 := by
      dsimp [B]
      push_cast
      nlinarith [sq_nonneg (k : ℝ), sq_nonneg (A : ℝ)]
    calc
      _ ≤ ‖z ^ 2‖ + ‖(((2 * (k + 1) + 1 : ℕ) : ℂ) / 2) ^ 2‖ := norm_add_le _ _
      _ = t ^ 2 + y ^ 2 + (((2 * (k + 1) + 1 : ℕ) : ℝ) / 2) ^ 2 := by
        rw [norm_pow, hzsq, norm_pow, norm_div]
        rw [Complex.norm_natCast, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
      _ ≤ B * u := by
        dsimp [u]
        nlinarith [mul_nonneg (sub_nonneg.mpr (show 1 ≤ B by linarith)) (sq_nonneg t)]
  have hprod : ‖∏ k ∈ Finset.range A,
      (z ^ 2 + (((2 * (k + 1) + 1 : ℕ) : ℂ) / 2) ^ 2)‖ ≤ (B * u) ^ A := by
    rw [norm_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfactor).trans_eq (by simp)
  change _ ≤ 4 * Real.exp (4 * |Real.log a|) * B ^ A
  unfold spectralABLExceptionalBase
  simp only [norm_mul, norm_div, norm_pow]
  calc
    _ ≤ (4 * Real.exp (4 * |Real.log a|) / u ^ (2 * A)) * (B * u) ^ A := by
      apply mul_le_mul _ hprod (norm_nonneg _) (by positivity)
      exact (div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hu _)
        (pow_le_pow_left₀ hu.le hden _)).trans
          (div_le_div_of_nonneg_right (by simpa only [norm_mul, z] using hphase) (pow_nonneg hu.le _))
    _ = (4 * Real.exp (4 * |Real.log a|) * B ^ A) / u ^ A := by
      rw [show 2 * A = A + A by omega, pow_add, mul_pow]
      field_simp
    _ ≤ _ := div_le_self (by positivity) (one_le_pow₀ (by dsimp [u]; nlinarith [sq_nonneg t]))

theorem spectralABLRegularCorrected_strip_bound (T Δ : ℝ) (hT : 0 < T) (hΔ : 0 < Δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      ‖spectralABLRegularCorrected T Δ ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨G, hG, hb⟩ := spectralABLCoshCancellation_strip_bound (3 / 4) (by norm_num) (by norm_num)
  refine ⟨(2 * Real.exp (1 / Δ ^ 2) / T ^ 2) * G, by positivity, ?_⟩
  intro t y hy
  rw [spectralABLRegularCorrected, norm_mul]
  exact mul_le_mul (spectralABLRegularBase_strip_bound T Δ hT hΔ t y (hy.trans (by norm_num)))
    (hb _ (by simpa using hy)) (norm_nonneg _) (by positivity)

theorem spectralABLExceptionalCorrected_strip_bound (a : ℝ) {A : ℕ} (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      ‖spectralABLExceptionalCorrected a A ((t : ℂ) + (y : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨G, hG, hb⟩ := spectralABLCoshCancellation_strip_bound (3 / 4) (by norm_num) (by norm_num)
  refine ⟨(4 * Real.exp (4 * |Real.log a|) * ((2 * (A : ℝ) + 3) ^ 2) ^ A) * G, by positivity, ?_⟩
  intro t y hy
  rw [spectralABLExceptionalCorrected, norm_mul]
  exact mul_le_mul (spectralABLExceptionalBase_strip_bound a hA t y (hy.trans (by norm_num)))
    (hb _ (by simpa using hy)) (norm_nonneg _) (by positivity)

end
end ArtinMatthews
