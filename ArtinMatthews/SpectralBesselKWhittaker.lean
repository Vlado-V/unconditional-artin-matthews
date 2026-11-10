module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKEquation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The actual square-root times K solution of the cusp Fourier ODE. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem spectralPositivePower_hasDerivAt (α : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ α)
      (α / (x : ℂ) * (x : ℂ) ^ α) x := by
  have hd := ((hasDerivAt_id (x : ℂ)).cpow_const (c := α)
    (Complex.ofReal_mem_slitPlane.mpr hx)).comp_ofReal
  convert hd using 1
  · rfl
  · simp only [id_eq, mul_one]
    rw [Complex.cpow_sub α 1 (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]
    ring

def spectralScaledBesselK (ν : ℂ) (q : ℝ) (y : ℝ) : ℂ :=
  schlafliBesselK ν (q * y)

theorem spectralScaledBesselK_hasDerivAt (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (spectralScaledBesselK ν q)
      ((q : ℂ) * deriv (schlafliBesselK ν) (q * y)) y := by
  have hk := schlafliBesselK_hasDerivAt ν (q * y) (mul_pos hq hy)
  rw [← schlafliBesselK_deriv ν (q * y) (mul_pos hq hy)] at hk
  have hd := hk.scomp y ((hasDerivAt_id y).const_mul q)
  convert hd using 1
  · rfl
  · simp only [mul_one, Complex.real_smul]

theorem spectralScaledBesselK_deriv (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    deriv (spectralScaledBesselK ν q) y =
      (q : ℂ) * deriv (schlafliBesselK ν) (q * y) :=
  (spectralScaledBesselK_hasDerivAt ν q y hq hy).deriv

theorem spectralScaledBesselK_deriv_hasDerivAt (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (spectralScaledBesselK ν q) t)
      ((q : ℂ) ^ 2 * deriv (fun t : ℝ => deriv (schlafliBesselK ν) t) (q * y)) y := by
  have hk := schlafliBesselK_deriv_hasDerivAt ν (q * y) (mul_pos hq hy)
  rw [← schlafliBesselK_second_deriv ν (q * y) (mul_pos hq hy)] at hk
  have hd := (hk.scomp y ((hasDerivAt_id y).const_mul q)).const_mul (q : ℂ)
  have hr : HasDerivAt (fun t : ℝ => (q : ℂ) * deriv (schlafliBesselK ν) (q * t))
      ((q : ℂ) ^ 2 * deriv (fun t : ℝ => deriv (schlafliBesselK ν) t) (q * y)) y := by
    convert hd using 1
    · rfl
    · simp only [mul_one, Complex.real_smul]
      ring
  apply hr.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with t ht
  exact spectralScaledBesselK_deriv ν q t hq ht

theorem spectralScaledBesselK_second_deriv (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y =
      (q : ℂ) ^ 2 * deriv (fun t : ℝ => deriv (schlafliBesselK ν) t) (q * y) :=
  (spectralScaledBesselK_deriv_hasDerivAt ν q y hq hy).deriv

theorem spectralScaledBesselK_differential_equation (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    (y : ℂ) ^ 2 * deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y +
      (y : ℂ) * deriv (spectralScaledBesselK ν q) y -
      (((q : ℂ) * y) ^ 2 + ν ^ 2) * spectralScaledBesselK ν q y = 0 := by
  rw [spectralScaledBesselK_second_deriv ν q y hq hy,
    spectralScaledBesselK_deriv ν q y hq hy]
  have he := schlafliBesselK_modifiedBesselODE ν (q * y) (mul_pos hq hy)
  simp only [Complex.ofReal_mul] at he
  unfold spectralScaledBesselK
  convert he using 1
  ring

def spectralKBesselWhittaker (ν : ℂ) (q : ℝ) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (1 / 2 : ℂ) * spectralScaledBesselK ν q y

theorem spectralKBesselWhittaker_eq_sqrt (ν : ℂ) (q y : ℝ) (hy : 0 ≤ y) :
    spectralKBesselWhittaker ν q y = (Real.sqrt y : ℂ) * schlafliBesselK ν (q * y) := by
  unfold spectralKBesselWhittaker spectralScaledBesselK
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hy]
  norm_num

theorem spectralKBesselWhittaker_hasDerivAt (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (spectralKBesselWhittaker ν q)
      ((y : ℂ) ^ (1 / 2 : ℂ) * (deriv (spectralScaledBesselK ν q) y +
        (1 / 2 : ℂ) / y * spectralScaledBesselK ν q y)) y := by
  have hp := spectralPositivePower_hasDerivAt (1 / 2) y hy
  have hg := spectralScaledBesselK_hasDerivAt ν q y hq hy
  rw [← spectralScaledBesselK_deriv ν q y hq hy] at hg
  convert hp.mul hg using 1
  · rfl
  · ring

theorem spectralKBesselWhittaker_deriv (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    deriv (spectralKBesselWhittaker ν q) y = (y : ℂ) ^ (1 / 2 : ℂ) *
      (deriv (spectralScaledBesselK ν q) y +
        (1 / 2 : ℂ) / y * spectralScaledBesselK ν q y) :=
  (spectralKBesselWhittaker_hasDerivAt ν q y hq hy).deriv

theorem spectralKBesselWhittaker_deriv_hasDerivAt (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => deriv (spectralKBesselWhittaker ν q) t)
      ((y : ℂ) ^ (1 / 2 : ℂ) *
        (deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y +
          1 / (y : ℂ) * deriv (spectralScaledBesselK ν q) y -
          (1 / 4 : ℂ) / (y : ℂ) ^ 2 * spectralScaledBesselK ν q y)) y := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hp := spectralPositivePower_hasDerivAt (1 / 2) y hy
  have hg := spectralScaledBesselK_hasDerivAt ν q y hq hy
  rw [← spectralScaledBesselK_deriv ν q y hq hy] at hg
  have hgd := spectralScaledBesselK_deriv_hasDerivAt ν q y hq hy
  rw [← spectralScaledBesselK_second_deriv ν q y hq hy] at hgd
  have hdiv := (hasDerivAt_const y (1 / 2 : ℂ)).div (hasDerivAt_id y).ofReal_comp hy0
  have hd := hp.mul (hgd.add (hdiv.mul hg))
  have hraw : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (1 / 2 : ℂ) *
      (deriv (spectralScaledBesselK ν q) t +
        (1 / 2 : ℂ) / t * spectralScaledBesselK ν q t))
      ((y : ℂ) ^ (1 / 2 : ℂ) *
        (deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y +
          1 / (y : ℂ) * deriv (spectralScaledBesselK ν q) y -
          (1 / 4 : ℂ) / (y : ℂ) ^ 2 * spectralScaledBesselK ν q y)) y := by
    convert hd using 1
    · rfl
    · simp only [Pi.add_apply, Pi.mul_apply, Pi.div_apply, id_eq, Complex.ofReal_one,
        zero_mul, mul_one, zero_sub]
      field_simp
      ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hy] with t ht
  exact spectralKBesselWhittaker_deriv ν q t hq ht

theorem spectralKBesselWhittaker_second_deriv (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (spectralKBesselWhittaker ν q) t) y =
      (y : ℂ) ^ (1 / 2 : ℂ) *
        (deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y +
          1 / (y : ℂ) * deriv (spectralScaledBesselK ν q) y -
          (1 / 4 : ℂ) / (y : ℂ) ^ 2 * spectralScaledBesselK ν q y) :=
  (spectralKBesselWhittaker_deriv_hasDerivAt ν q y hq hy).deriv

theorem spectralKBesselWhittaker_fourierODE (ν : ℂ) (q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    -((y : ℂ) ^ 2) *
        (deriv (fun t : ℝ => deriv (spectralKBesselWhittaker ν q) t) y -
          (q : ℂ) ^ 2 * spectralKBesselWhittaker ν q y) =
      (1 / 4 - ν ^ 2) * spectralKBesselWhittaker ν q y := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [spectralKBesselWhittaker_second_deriv ν q y hq hy]
  unfold spectralKBesselWhittaker
  have he := spectralScaledBesselK_differential_equation ν q y hq hy
  calc
    _ = (1 / 4 - ν ^ 2) *
        ((y : ℂ) ^ (1 / 2 : ℂ) * spectralScaledBesselK ν q y) -
        (y : ℂ) ^ (1 / 2 : ℂ) *
        ((y : ℂ) ^ 2 * deriv (fun t : ℝ => deriv (spectralScaledBesselK ν q) t) y +
          (y : ℂ) * deriv (spectralScaledBesselK ν q) y -
          (((q : ℂ) * y) ^ 2 + ν ^ 2) * spectralScaledBesselK ν q y) := by
      field_simp [hy0]
      ring
    _ = _ := by rw [he, mul_zero, sub_zero]

theorem spectralKBesselWhittaker_imaginary_fourierODE (r q y : ℝ)
    (hq : 0 < q) (hy : 0 < y) :
    -((y : ℂ) ^ 2) *
        (deriv (fun t : ℝ => deriv (spectralKBesselWhittaker (r * Complex.I) q) t) y -
          (q : ℂ) ^ 2 * spectralKBesselWhittaker (r * Complex.I) q y) =
      ((1 / 4 + r ^ 2 : ℝ) : ℂ) * spectralKBesselWhittaker (r * Complex.I) q y := by
  have h := spectralKBesselWhittaker_fourierODE (r * Complex.I) q y hq hy
  convert h using 1
  push_cast
  rw [mul_pow, Complex.I_sq]
  ring

end ArtinMatthews
