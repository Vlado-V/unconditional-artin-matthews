module

public import ArtinMatthews.SpectralJRegularizedWeight
public import ArtinMatthews.SpectralGammaThreeQuarterStrip
public import ArtinMatthews.SpectralJForwardStripRapid
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set Complex
open scoped ContDiff
noncomputable section

private theorem spectralJRegularizedWeight_rapid_of_primitive_bound
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L B U : ℝ) (hB : B ≤ 3 / 4) (hU : 0 ≤ U)
    (hu : ∀ t y : ℝ, |y| ≤ B →
      ‖spectralJRegularizerPrimitive L (((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4)‖ ≤ U)
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ B →
      (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t|) *
        ‖spectralJRegularizedWeight f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨A, hA, ha⟩ := spectralJForwardTransform_strip_rapid f hf hc hp (2 * (N + 2))
  obtain ⟨G, hG, hg⟩ := spectralABLCoshCancellation_exp_strip_bound
  refine ⟨Real.pi * G * U * A, by positivity, ?_⟩
  intro t y hy
  let z : ℂ := (t : ℂ) + (y : ℂ) * I
  have hy' : |y| ≤ 3 / 4 := hy.trans hB
  have hz : |z.im| ≤ 3 / 4 := by simpa [z] using hy'
  have hat : ‖spectralJForwardTransform f z‖ ≤ A / (1 + |t|) ^ (2 * (N + 2)) := by
    simpa [z] using ha z hz
  have hpoly : (1 + t ^ 2) ^ (N + 2) ≤ (1 + |t|) ^ (2 * (N + 2)) := by
    have hbase : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
      nlinarith only [sq_abs t, abs_nonneg t]
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + t ^ 2) hbase (N + 2)
  have hb : (1 + t ^ 2) ^ (N + 2) * ‖spectralJForwardTransform f z‖ ≤ A := by
    have ht := (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ (2 * (N + 2)))).mp hat
    exact (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)).trans (by simpa [mul_comm] using ht)
  have hg' : Real.exp (Real.pi * |t|) * ‖spectralABLCoshCancellation z‖ ≤ G * (1 + t ^ 2) ^ 2 :=
    hg t y hy'
  have hu' : ‖spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)‖ ≤ U := hu t y hy
  calc
    _ = Real.pi * ((1 + t ^ 2) ^ N * ‖spectralJForwardTransform f z‖) *
        (Real.exp (Real.pi * |t|) * ‖spectralABLCoshCancellation z‖) *
        ‖spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)‖ := by
      rw [spectralJRegularizedWeight, norm_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      ring
    _ ≤ Real.pi * ((1 + t ^ 2) ^ N * ‖spectralJForwardTransform f z‖) *
        (G * (1 + t ^ 2) ^ 2) * U := by gcongr
    _ = Real.pi * G * U * ((1 + t ^ 2) ^ (N + 2) * ‖spectralJForwardTransform f z‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

private theorem spectralJ_regularizer_argument_re (t y : ℝ) :
    ((((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4) : ℂ).re = t ^ 2 - y ^ 2 + 1 / 4 := by
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  <;> ring

theorem spectralJRegularizedWeight_normalized_rapid (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L : ℝ) (hL : 0 ≤ L) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t|) *
        ‖spectralJRegularizedWeight f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  apply spectralJRegularizedWeight_rapid_of_primitive_bound f hf hc hp L (3 / 4)
    (L * Real.exp (L * (5 / 16))) le_rfl (by positivity)
  intro t y hy
  apply spectralJRegularizerPrimitive_norm_le L (5 / 16) hL (by norm_num)
  rw [spectralJ_regularizer_argument_re]
  have hy2 := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 3 / 4)).mpr hy
  rw [sq_abs] at hy2
  nlinarith only [hy2, sq_nonneg t]

theorem spectralJRegularizedWeight_inner_uniform_rapid (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ t y : ℝ, |y| ≤ 3 / 8 →
      (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t|) *
        ‖spectralJRegularizedWeight f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨A, hA, ha⟩ := spectralJForwardTransform_strip_rapid f hf hc hp (2 * (N + 2))
  obtain ⟨G, hG, hg⟩ := spectralABLCoshCancellation_exp_strip_bound
  let C : ℝ := Real.pi * G * (128 / 7) * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro L hL
  have hu (t y : ℝ) (hy : |y| ≤ 3 / 8) :
      ‖spectralJRegularizerPrimitive L (((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4)‖ ≤ 128 / 7 := by
    have harg : (7 / 64 : ℝ) ≤ ((((t : ℂ) + (y : ℂ) * I) ^ 2 + 1 / 4) : ℂ).re := by
      rw [spectralJ_regularizer_argument_re]
      have hy2 := (sq_le_sq₀ (abs_nonneg y) (by norm_num : (0 : ℝ) ≤ 3 / 8)).mpr hy
      rw [sq_abs] at hy2
      nlinarith only [hy2, sq_nonneg t]
    convert spectralJRegularizerPrimitive_norm_le_of_re_pos L (7 / 64) hL
      (by norm_num) _ harg using 1 <;> norm_num
  intro t y hy
  have hy' : |y| ≤ 3 / 4 := hy.trans (by norm_num)
  let z : ℂ := (t : ℂ) + (y : ℂ) * I
  have hat : ‖spectralJForwardTransform f z‖ ≤ A / (1 + |t|) ^ (2 * (N + 2)) := by
    simpa [z] using ha z (by simpa [z] using hy')
  have hpoly : (1 + t ^ 2) ^ (N + 2) ≤ (1 + |t|) ^ (2 * (N + 2)) := by
    have hbase : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by nlinarith only [sq_abs t, abs_nonneg t]
    simpa only [← pow_mul] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 + t ^ 2) hbase (N + 2)
  have hb : (1 + t ^ 2) ^ (N + 2) * ‖spectralJForwardTransform f z‖ ≤ A := by
    have ht := (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ (2 * (N + 2)))).mp hat
    exact (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)).trans (by simpa [z, mul_comm] using ht)
  have hg' := hg t y hy'
  have hu' := hu t y hy
  change (1 + t ^ 2) ^ N * Real.exp (Real.pi * |t|) * ‖spectralJRegularizedWeight f L z‖ ≤ C
  calc
    _ = Real.pi * ((1 + t ^ 2) ^ N * ‖spectralJForwardTransform f z‖) *
        (Real.exp (Real.pi * |t|) * ‖spectralABLCoshCancellation z‖) *
        ‖spectralJRegularizerPrimitive L (z ^ 2 + 1 / 4)‖ := by
      rw [spectralJRegularizedWeight, norm_mul, norm_mul, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      ring
    _ ≤ Real.pi * ((1 + t ^ 2) ^ N * ‖spectralJForwardTransform f z‖) *
        (G * (1 + t ^ 2) ^ 2) * (128 / 7) := by gcongr
    _ = Real.pi * G * (128 / 7) * ((1 + t ^ 2) ^ (N + 2) * ‖spectralJForwardTransform f z‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

theorem spectralJRegularizedWeight_strip_bound (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t y : ℝ, |y| ≤ 3 / 4 →
      ‖spectralJRegularizedWeight f L ((t : ℂ) + (y : ℂ) * I)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := spectralJRegularizedWeight_normalized_rapid f hf hc hp L hL 0
  refine ⟨C, hC, fun t y hy => ?_⟩
  have hE : 1 ≤ Real.exp (Real.pi * |t|) := Real.one_le_exp (by positivity)
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right hE (norm_nonneg _)).trans (by simpa using hb t y hy)

end
end ArtinMatthews
