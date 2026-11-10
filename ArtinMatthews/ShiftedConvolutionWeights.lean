module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import ArtinMatthews.ShiftedConvolutionAbel
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
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth dyadic cutoff and Mellin-height bounds for the sampled variation
used in (5.6). The phase is the actual positive-real power n^(-it). -/

noncomputable section
open Complex Real Set Finset
open scoped ContDiff

namespace ArtinMatthews

/-- The unitary Mellin phase, with an immaterial totalized value at zero. -/
def shiftedMellinPhase (t x : ℝ) : ℂ := Complex.exp (Complex.I * (-(t * Real.log x) : ℝ))

@[simp] theorem norm_shiftedMellinPhase (t x : ℝ) : ‖shiftedMellinPhase t x‖ = 1 := by
  simp [shiftedMellinPhase, Complex.norm_exp]

/-- On the positive axis this is exactly the complex power x^(-it). -/
theorem shiftedMellinPhase_eq_cpow (t x : ℝ) (hx : 0 < x) :
    shiftedMellinPhase t x = (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le]
  unfold shiftedMellinPhase
  congr 1
  push_cast
  ring

/-- The sampled coefficient weight in the paper. -/
def shiftedDyadicWeight (w : ℝ → ℂ) (K t : ℝ) (n : ℕ) : ℂ :=
  shiftedMellinPhase t n * w ((n : ℝ) / K)

/-- A cutoff above the dyadic support [K,2K]. -/
def shiftedDyadicLength (K : ℝ) : ℕ := ⌈2 * K⌉₊ + 1

private theorem phase_difference_le (t x y : ℝ) :
    ‖shiftedMellinPhase t x - shiftedMellinPhase t y‖ ≤
      |t| * |Real.log x - Real.log y| := by
  have he : shiftedMellinPhase t x - shiftedMellinPhase t y =
      shiftedMellinPhase t y *
        (Complex.exp (Complex.I * (-(t * (Real.log x - Real.log y)) : ℝ)) - 1) := by
    unfold shiftedMellinPhase
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, norm_shiftedMellinPhase, one_mul]
  convert (norm_exp_I_mul_ofReal_sub_one_le
    (x := -(t * (Real.log x - Real.log y)))) using 1
  rw [Real.norm_eq_abs, abs_neg, abs_mul]

private theorem phase_nat_difference_le (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ‖shiftedMellinPhase t n - shiftedMellinPhase t (n + 1)‖ ≤ |t| / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : |Real.log (n : ℝ) - Real.log ((n : ℝ) + 1)| ≤ 1 / n := by
    rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hn0 (by linarith)))]
    have hb := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0 < (n : ℝ) + 1) hn0)
    rw [Real.log_div (by positivity) hn0.ne'] at hb
    have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    rw [he] at hb
    linarith
  exact (phase_difference_le t n (n + 1)).trans (by
    simpa only [div_eq_mul_inv, mul_one, one_mul] using mul_le_mul_of_nonneg_left hlog (abs_nonneg t))

private theorem schwartz_lipschitz (w : SchwartzMap ℝ ℂ) (x y : ℝ) :
    ‖w x - w y‖ ≤ SchwartzMap.seminorm ℝ 0 1 w * |x - y| := by
  have hderiv (z : ℝ) : ‖deriv w z‖ ≤ SchwartzMap.seminorm ℝ 0 1 w := by
    simpa using SchwartzMap.le_seminorm' ℝ 0 1 w z
  simpa only [Real.norm_eq_abs] using
    (convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun z _ ↦ (w.smooth ⊤).differentiable (by simp) z) (fun z _ ↦ hderiv z)
      (mem_univ y) (mem_univ x))

/-- The dyadic length is comparable to the real scale, uniformly down to K=1. -/
theorem shiftedDyadicLength_bounds (K : ℝ) (hK : 1 ≤ K) :
    2 ≤ shiftedDyadicLength K ∧ (shiftedDyadicLength K : ℝ) ≤ 4 * K := by
  have hceil := Nat.le_ceil (2 * K)
  have hceil' := Nat.ceil_lt_add_one (by linarith : 0 ≤ 2 * K)
  constructor
  · unfold shiftedDyadicLength
    have : 1 ≤ ⌈2 * K⌉₊ := by
      by_contra h
      have : ⌈2 * K⌉₊ = 0 := by omega
      rw [this] at hceil
      norm_num at hceil
      linarith
    omega
  · unfold shiftedDyadicLength
    push_cast
    linarith

/-- Each dyadic sample difference costs only (1+|t|)/K. -/
theorem shiftedDyadicWeight_difference (w : SchwartzMap ℝ ℂ)
    (hw : Function.support w ⊆ Icc 1 2) (K t : ℝ) (hK : 1 ≤ K) (n : ℕ) :
    ‖shiftedDyadicWeight w K t n - shiftedDyadicWeight w K t (n + 1)‖ ≤
      (SchwartzMap.seminorm ℝ 0 1 w + 2 * |t| * SchwartzMap.seminorm ℝ 0 0 w) / K := by
  let B := SchwartzMap.seminorm ℝ 0 0 w
  let L := SchwartzMap.seminorm ℝ 0 1 w
  have hB : 0 ≤ B := apply_nonneg _ _
  have hL : 0 ≤ L := apply_nonneg _ _
  have hK0 : 0 < K := by linarith
  have he : shiftedDyadicWeight w K t n - shiftedDyadicWeight w K t (n + 1) =
      shiftedMellinPhase t n * (w ((n : ℝ) / K) - w (((n : ℝ) + 1) / K)) +
      (shiftedMellinPhase t n - shiftedMellinPhase t ((n : ℝ) + 1)) * w (((n : ℝ) + 1) / K) := by
    simp only [shiftedDyadicWeight, Nat.cast_add, Nat.cast_one]
    ring
  have hw1 : ‖w ((n : ℝ) / K) - w (((n : ℝ) + 1) / K)‖ ≤ L / K := by
    apply (schwartz_lipschitz w _ _).trans_eq
    have hs : (n : ℝ) / K - ((n : ℝ) + 1) / K = -(1 / K) := by ring
    rw [hs, abs_neg, abs_of_pos (one_div_pos.mpr hK0)]
    dsimp [L]
    ring
  have hw2 : ‖(shiftedMellinPhase t n - shiftedMellinPhase t ((n : ℝ) + 1)) *
      w (((n : ℝ) + 1) / K)‖ ≤ 2 * |t| * B / K := by
    by_cases hz : w (((n : ℝ) + 1) / K) = 0
    · rw [hz, mul_zero, norm_zero]
      positivity
    · have hsupport := (hw hz).1
      have hKn : K ≤ (n : ℝ) + 1 := by simpa using (le_div_iff₀ hK0).mp hsupport
      rcases n with _ | n
      · simp [shiftedMellinPhase]
        positivity
      · have hn : (0 : ℝ) < n + 1 := by positivity
        have htwo : K ≤ 2 * ((n : ℝ) + 1) := by push_cast at hKn; linarith
        rw [norm_mul]
        calc
          _ ≤ (|t| / ((n : ℝ) + 1)) * B := by
            apply mul_le_mul
            · simpa only [Nat.cast_add, Nat.cast_one] using phase_nat_difference_le t (n + 1) (by omega)
            · exact SchwartzMap.norm_le_seminorm ℝ w _
            · exact norm_nonneg _
            · positivity
          _ ≤ 2 * |t| * B / K := by
            apply (le_div_iff₀ hK0).mpr
            have hmul := mul_le_mul_of_nonneg_left htwo (div_nonneg (abs_nonneg t) hn.le)
            have heq : |t| / ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) = 2 * |t| := by field_simp
            rw [heq] at hmul
            have := mul_le_mul_of_nonneg_right hmul hB
            nlinarith
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ L / K + 2 * |t| * B / K := by
      apply add_le_add _ hw2
      simpa only [norm_mul, norm_shiftedMellinPhase, one_mul] using hw1
    _ = _ := by dsimp [L, B]; ring

/-- Uniform sampled variation, with its dependence on two fixed cutoff seminorms explicit. -/
theorem shiftedDyadicWeight_variation (w : SchwartzMap ℝ ℂ)
    (hw : Function.support w ⊆ Icc 1 2) (K t : ℝ) (hK : 1 ≤ K) :
    sampledVariation (shiftedDyadicLength K) (shiftedDyadicWeight w K t) ≤
      (9 * SchwartzMap.seminorm ℝ 0 0 w + 4 * SchwartzMap.seminorm ℝ 0 1 w) * (1 + |t|) := by
  let B := SchwartzMap.seminorm ℝ 0 0 w
  let L := SchwartzMap.seminorm ℝ 0 1 w
  have hB : 0 ≤ B := apply_nonneg _ _
  have hL : 0 ≤ L := apply_nonneg _ _
  have hK0 : 0 < K := by linarith
  have hN := (shiftedDyadicLength_bounds K hK).2
  unfold sampledVariation
  have hlast : ‖shiftedDyadicWeight w K t (shiftedDyadicLength K)‖ ≤ B := by
    simpa only [shiftedDyadicWeight, norm_mul, norm_shiftedMellinPhase, one_mul] using
      SchwartzMap.norm_le_seminorm ℝ w ((shiftedDyadicLength K : ℝ) / K)
  have hsum : (∑ n ∈ range (shiftedDyadicLength K),
      ‖shiftedDyadicWeight w K t n - shiftedDyadicWeight w K t (n + 1)‖) ≤ 4 * (L + 2 * |t| * B) := by
    calc
      _ ≤ ∑ _n ∈ range (shiftedDyadicLength K), (L + 2 * |t| * B) / K :=
        sum_le_sum (fun n _ ↦ shiftedDyadicWeight_difference w hw K t hK n)
      _ = (shiftedDyadicLength K : ℝ) * ((L + 2 * |t| * B) / K) := by simp
      _ ≤ (4 * K) * ((L + 2 * |t| * B) / K) := mul_le_mul_of_nonneg_right hN (by positivity)
      _ = _ := by field_simp
  dsimp [B, L] at hlast hsum ⊢
  nlinarith [mul_nonneg (abs_nonneg t) hB, mul_nonneg (abs_nonneg t) hL]

end ArtinMatthews
