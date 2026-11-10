module

public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicSpace
public import ArtinMatthews.SpectralBesselKRecurrence
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The modified Bessel equation for the existing arbitrary-order Schläfli K. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

theorem schlafliIntegral_deriv (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (schlafliIntegral ν) x = -((x : ℂ) / 2) * schlafliIntegral (ν - 1) x :=
  (schlafliIntegral_hasDerivAt_all_orders ν x hx).deriv

theorem schlafliIntegral_deriv_hasDerivAt (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => deriv (schlafliIntegral ν) y)
      (-(1 / 2 : ℂ) * schlafliIntegral (ν - 1) x +
        (x : ℂ) ^ 2 / 4 * schlafliIntegral (ν - 1 - 1) x) x := by
  have h := (((hasDerivAt_id x).ofReal_comp.div_const 2).neg).mul
    (schlafliIntegral_hasDerivAt_all_orders (ν - 1) x hx)
  have hd : HasDerivAt (fun y : ℝ => -((y : ℂ) / 2) * schlafliIntegral (ν - 1) y)
      (-(1 / 2 : ℂ) * schlafliIntegral (ν - 1) x +
        (x : ℂ) ^ 2 / 4 * schlafliIntegral (ν - 1 - 1) x) x := by
    convert h using 1
    · rfl
    · simp only [id_eq, Pi.neg_apply, Complex.ofReal_one]
      ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact schlafliIntegral_deriv ν y hy

theorem schlafliIntegral_second_deriv (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x =
      -(1 / 2 : ℂ) * schlafliIntegral (ν - 1) x +
        (x : ℂ) ^ 2 / 4 * schlafliIntegral (ν - 1 - 1) x :=
  (schlafliIntegral_deriv_hasDerivAt ν x hx).deriv

theorem schlafliIntegral_differential_equation (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ 2 * deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
        (2 * ν - 1) * x * deriv (schlafliIntegral ν) x -
        (x : ℂ) ^ 2 * schlafliIntegral ν x = 0 := by
  rw [schlafliIntegral_second_deriv ν x hx, schlafliIntegral_deriv ν x hx]
  have h := schlafliIntegral_recurrence (ν - 1) x hx
  rw [sub_add_cancel] at h
  linear_combination -(x : ℂ) ^ 2 * h

def spectralSchlafliPrefactor (ν : ℂ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ((x : ℂ) / 2) ^ (-ν)

theorem spectralSchlafliPrefactor_hasDerivAt (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (spectralSchlafliPrefactor ν)
      (-(ν / (x : ℂ)) * spectralSchlafliPrefactor ν x) x := by
  have hb : (x : ℂ) / 2 ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')
    (by norm_num)
  have hs : (x : ℂ) / 2 ∈ Complex.slitPlane := by
    have h := Complex.ofReal_mem_slitPlane.mpr (show 0 < x / 2 by positivity)
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using h
  have hd := (((hasDerivAt_id (x : ℂ)).div_const 2).cpow_const
    (c := -ν) hs).comp_ofReal.const_mul (1 / 2 : ℂ)
  convert hd using 1
  · rfl
  · unfold spectralSchlafliPrefactor
    simp only [id_eq]
    rw [Complex.cpow_sub (-ν) 1 hb, Complex.cpow_one]
    field_simp

theorem schlafliBesselK_hasDerivAt (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (schlafliBesselK ν)
      (spectralSchlafliPrefactor ν x *
        (deriv (schlafliIntegral ν) x - ν / (x : ℂ) * schlafliIntegral ν x)) x := by
  have hd := (spectralSchlafliPrefactor_hasDerivAt ν x hx).mul
    (schlafliIntegral_hasDerivAt_all_orders ν x hx)
  rw [← schlafliIntegral_deriv ν x hx] at hd
  convert hd using 1
  · rfl
  · ring

theorem schlafliBesselK_deriv (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (schlafliBesselK ν) x = spectralSchlafliPrefactor ν x *
      (deriv (schlafliIntegral ν) x - ν / (x : ℂ) * schlafliIntegral ν x) :=
  (schlafliBesselK_hasDerivAt ν x hx).deriv

theorem schlafliBesselK_deriv_hasDerivAt (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => deriv (schlafliBesselK ν) y)
      (spectralSchlafliPrefactor ν x *
        (deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
          2 * ν / (x : ℂ) * deriv (schlafliIntegral ν) x +
          ν * (ν + 1) / (x : ℂ) ^ 2 * schlafliIntegral ν x)) x := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hdiv := (hasDerivAt_const x ν).div (hasDerivAt_id x).ofReal_comp hx0
  have hq := (schlafliIntegral_deriv_hasDerivAt ν x hx).sub
    (hdiv.mul (schlafliIntegral_hasDerivAt_all_orders ν x hx))
  have hd := (spectralSchlafliPrefactor_hasDerivAt ν x hx).mul hq
  rw [← schlafliIntegral_deriv ν x hx, ← schlafliIntegral_second_deriv ν x hx] at hd
  have hraw : HasDerivAt (fun y : ℝ => spectralSchlafliPrefactor ν y *
      (deriv (schlafliIntegral ν) y - ν / (y : ℂ) * schlafliIntegral ν y))
      (spectralSchlafliPrefactor ν x *
        (deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
          2 * ν / (x : ℂ) * deriv (schlafliIntegral ν) x +
          ν * (ν + 1) / (x : ℂ) ^ 2 * schlafliIntegral ν x)) x := by
    convert hd using 1
    · rfl
    · simp only [Pi.sub_apply, Pi.mul_apply, Pi.div_apply, id_eq, Complex.ofReal_one,
        zero_mul, mul_one, zero_sub]
      field_simp
      ring
  apply hraw.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with y hy
  exact schlafliBesselK_deriv ν y hy

theorem schlafliBesselK_second_deriv (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => deriv (schlafliBesselK ν) y) x =
      spectralSchlafliPrefactor ν x *
        (deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
          2 * ν / (x : ℂ) * deriv (schlafliIntegral ν) x +
          ν * (ν + 1) / (x : ℂ) ^ 2 * schlafliIntegral ν x) :=
  (schlafliBesselK_deriv_hasDerivAt ν x hx).deriv

theorem schlafliBesselK_modifiedBesselODE (ν : ℂ) (x : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ 2 * deriv (fun y : ℝ => deriv (schlafliBesselK ν) y) x +
      (x : ℂ) * deriv (schlafliBesselK ν) x -
      ((x : ℂ) ^ 2 + ν ^ 2) * schlafliBesselK ν x = 0 := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [schlafliBesselK_second_deriv ν x hx, schlafliBesselK_deriv ν x hx]
  change (x : ℂ) ^ 2 * (spectralSchlafliPrefactor ν x *
      (deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
        2 * ν / (x : ℂ) * deriv (schlafliIntegral ν) x +
        ν * (ν + 1) / (x : ℂ) ^ 2 * schlafliIntegral ν x)) +
    (x : ℂ) * (spectralSchlafliPrefactor ν x *
      (deriv (schlafliIntegral ν) x - ν / (x : ℂ) * schlafliIntegral ν x)) -
    ((x : ℂ) ^ 2 + ν ^ 2) *
      (spectralSchlafliPrefactor ν x * schlafliIntegral ν x) = 0
  calc
    _ = spectralSchlafliPrefactor ν x *
        ((x : ℂ) ^ 2 * deriv (fun y : ℝ => deriv (schlafliIntegral ν) y) x -
          (2 * ν - 1) * x * deriv (schlafliIntegral ν) x -
          (x : ℂ) ^ 2 * schlafliIntegral ν x) := by
      field_simp [hx0]
      ring
    _ = 0 := by rw [schlafliIntegral_differential_equation ν x hx, mul_zero]

end ArtinMatthews
