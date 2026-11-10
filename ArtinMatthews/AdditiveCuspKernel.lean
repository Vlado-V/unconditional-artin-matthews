module

public import ArtinMatthews.AdditiveCuspHorizontal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
# Pointwise bounds for exponentially weighted Dirichlet kernels

The geometric-sum identity gives decay away from integer frequencies. These
are actual finite-sum estimates used in the convolution proof of (5.4).
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Complex

namespace ArtinMatthews

/-- Moving a point of the unit circle radially outward cannot decrease its
Euclidean distance from one. -/
theorem norm_sub_one_le_norm_radial_sub_one {z : ℂ} (hz : ‖z‖ = 1)
    {r : ℝ} (hr : 1 ≤ r) : ‖z - 1‖ ≤ ‖(r : ℂ) * z - 1‖ := by
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    simpa [Complex.normSq_apply, hz, pow_two] using Complex.normSq_eq_norm_sq z
  have hsq : ‖(r : ℂ) * z - 1‖ ^ 2 =
      (r - 1) ^ 2 + r * ‖z - 1‖ ^ 2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re, one_im]
    nlinarith [hzsq]
  have hn := sq_nonneg ‖z - 1‖
  have hp := mul_nonneg (sub_nonneg.mpr hr) hn
  nlinarith [sq_nonneg (r - 1), norm_nonneg ((r : ℂ) * z - 1), norm_nonneg (z - 1)]

/-- The geometric kernel is bounded by its number of terms times its largest
possible radial weight. -/
theorem norm_geometricKernel_le_card {z : ℂ} (hz : ‖z‖ = 1)
    {r : ℝ} (hr : 1 ≤ r) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ((r : ℂ) * z) ^ n‖ ≤ (N : ℝ) * r ^ N := by
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖((r : ℂ) * z) ^ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, r ^ N := by
      apply Finset.sum_le_sum
      intro n hn
      simp only [norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ r), hz, mul_one]
      exact pow_le_pow_right₀ hr (Finset.mem_range.mp hn).le
    _ = _ := by simp

/-- Cancellation in the geometric sum gives an inverse-distance bound. -/
theorem norm_geometricKernel_le_inverse_distance {z : ℂ} (hz : ‖z‖ = 1)
    {r d : ℝ} (hr : 1 ≤ r) (hd : 0 < d) (hdz : d ≤ ‖z - 1‖) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ((r : ℂ) * z) ^ n‖ ≤ (r ^ N + 1) / d := by
  have hden : d ≤ ‖(r : ℂ) * z - 1‖ :=
    hdz.trans (norm_sub_one_le_norm_radial_sub_one hz hr)
  have hne : (r : ℂ) * z ≠ 1 := by
    intro heq
    simp [heq] at hden
    linarith
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div₀ (by positivity)
  · calc
      ‖((r : ℂ) * z) ^ N - 1‖ ≤ ‖((r : ℂ) * z) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = _ := by simp [hz, abs_of_nonneg (show 0 ≤ r by linarith)]
  · exact hd
  · exact hden

/-- On the half-period, the Fourier phase has distance at least `4t` from one. -/
theorem fourier_one_sub_one_lower {t : ℝ} (ht : 0 ≤ t) (htop : t ≤ 1 / 2) :
    4 * t ≤ ‖fourier 1 (t : AddCircle (1 : ℝ)) - 1‖ := by
  have hsin : 2 * t ≤ Real.sin (Real.pi * t) := by
    have h := Real.mul_le_sin (x := Real.pi * t) (by positivity)
      (by nlinarith [Real.pi_pos])
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at h
    nlinarith [Real.pi_pos]
  have heq : fourier 1 (t : AddCircle (1 : ℝ)) =
      Complex.exp (Complex.I * (2 * Real.pi * t : ℝ)) := by
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : (2 * Real.pi * t) / 2 = Real.pi * t := by ring
  rw [hhalf, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 2 * Real.sin (Real.pi * t))]
  linarith

/-- Natural Fourier frequencies are powers of the fundamental frequency. -/
theorem fourier_nat_eq_pow (n : ℕ) (t : ℝ) :
    fourier (n : ℤ) (t : AddCircle (1 : ℝ)) =
      fourier 1 (t : AddCircle (1 : ℝ)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

/-- The phase at a reflected point is the conjugate phase. -/
theorem fourier_one_sub_real (n : ℤ) (t : ℝ) :
    fourier n ((1 - t : ℝ) : AddCircle (1 : ℝ)) =
      conj (fourier n (t : AddCircle (1 : ℝ))) := by
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  simp only [fourier_apply, smul_neg, fourier_neg']

/-- The natural exponential weight is exactly a geometric radial factor. -/
theorem weighted_fourier_term_eq_pow (n : ℕ) (y t : ℝ) :
    (Real.exp (2 * Real.pi * n * y) : ℂ) *
        fourier (n : ℤ) (t : AddCircle (1 : ℝ)) =
      ((Real.exp (2 * Real.pi * y) : ℂ) * fourier 1 (t : AddCircle (1 : ℝ))) ^ n := by
  have he : 2 * Real.pi * (n : ℝ) * y = (n : ℝ) * (2 * Real.pi * y) := by ring
  rw [mul_pow, fourier_nat_eq_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul, he]

/-- At height `1/N`, the outer radial factor is independent of `N`. -/
theorem exponential_radius_pow (N : ℕ) (hN : 0 < N) :
    Real.exp (2 * Real.pi * (1 / (N : ℝ))) ^ N = Real.exp (2 * Real.pi) := by
  rw [← Real.exp_nat_mul]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The compensating Fourier kernel is a finite geometric sum. -/
theorem weightedFourierKernel_eq_geometric (N : ℕ) (y t : ℝ) :
    weightedFourierKernel N y t =
      ∑ n ∈ Finset.range N,
        ((Real.exp (2 * Real.pi * y) : ℂ) * fourier 1 (t : AddCircle (1 : ℝ))) ^ n := by
  simp only [weightedFourierKernel, weighted_fourier_term_eq_pow]

/-- The norm of the kernel is symmetric about the half-period. -/
theorem norm_weightedFourierKernel_one_sub (N : ℕ) (y t : ℝ) :
    ‖weightedFourierKernel N y (1 - t)‖ = ‖weightedFourierKernel N y t‖ := by
  have heq : weightedFourierKernel N y (1 - t) = conj (weightedFourierKernel N y t) := by
    simp only [weightedFourierKernel, map_sum, map_mul, Complex.conj_ofReal,
      fourier_one_sub_real]
  rw [heq, Complex.norm_conj]

/-- Uniform flat bound on the kernel at height `1/N`. -/
theorem norm_weightedFourierKernel_le_flat (N : ℕ) (hN : 0 < N) (t : ℝ) :
    ‖weightedFourierKernel N (1 / (N : ℝ)) t‖ ≤
      (Real.exp (2 * Real.pi) + 1) * N := by
  rw [weightedFourierKernel_eq_geometric]
  have hr : 1 ≤ Real.exp (2 * Real.pi * (1 / (N : ℝ))) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have h := norm_geometricKernel_le_card
    (z := fourier 1 (t : AddCircle (1 : ℝ))) (Circle.norm_coe _) hr N
  rw [exponential_radius_pow N hN] at h
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- Away from the singular endpoint, the kernel has reciprocal decay. -/
theorem norm_weightedFourierKernel_le_reciprocal (N : ℕ) (hN : 0 < N)
    {t : ℝ} (ht : 0 < t) (htop : t ≤ 1 / 2) :
    ‖weightedFourierKernel N (1 / (N : ℝ)) t‖ ≤
      (Real.exp (2 * Real.pi) + 1) / t := by
  rw [weightedFourierKernel_eq_geometric]
  have hr : 1 ≤ Real.exp (2 * Real.pi * (1 / (N : ℝ))) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have h := norm_geometricKernel_le_inverse_distance
    (z := fourier 1 (t : AddCircle (1 : ℝ))) (Circle.norm_coe _) hr
    (show 0 < 4 * t by positivity) (fourier_one_sub_one_lower ht.le htop) N
  rw [exponential_radius_pow N hN] at h
  exact h.trans (div_le_div_of_nonneg_left (by positivity) ht (by linarith))

/-- The weighted kernel has period one. -/
theorem weightedFourierKernel_periodic (N : ℕ) (y : ℝ) :
    Function.Periodic (weightedFourierKernel N y) 1 := by
  intro t
  simp only [weightedFourierKernel, AddCircle.coe_add_period]

end ArtinMatthews
