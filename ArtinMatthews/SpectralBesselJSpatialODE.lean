module

public import ArtinMatthews.SpectralRegularizedBesselSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv


set_option backward.privateInPublic true
@[expose] public section

/-! The literal Bessel J order recurrence and spatial differential equation
on the positive ray, with no restriction on complex order. -/
noncomputable section
open Complex Set Filter
open scoped Topology

namespace ArtinMatthews

local notation "F(" b ")" => Complex.regularizedHGFun 0 {b}

theorem spectral_besselJ_order_recurrence (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    Complex.besselJ ν (x : ℂ) =
      (2*(ν+1)/(x : ℂ))*Complex.besselJ (ν+1) (x : ℂ) -
        Complex.besselJ (ν+2) (x : ℂ) := by
  let b := (x : ℂ)/2
  let w := -b^2
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hb : b ≠ 0 := div_ne_zero hxC (by norm_num)
  have h₁ : b^(ν+1) = b^ν*b := by rw [Complex.cpow_add ν 1 hb, Complex.cpow_one]
  have h₂ : b^(ν+2) = b^ν*b^2 := by
    rw [Complex.cpow_add ν 2 hb, ← Complex.cpow_natCast b 2]
    norm_num
  change b^ν*F(ν+1) w =
    (2*(ν+1)/(x : ℂ))*(b^(ν+1)*F(ν+1+1) w) - b^(ν+2)*F(ν+2+1) w
  rw [spectral_regularizedBessel_contiguous (ν+1) w, h₁, h₂,
    show ν+1+2 = ν+2+1 by ring]
  dsimp only [w, b]
  field_simp [hxC] <;> ring

theorem spectral_besselJ_spatial_hasDerivAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Complex.besselJ ν (y : ℂ))
      ((ν/(x : ℂ))*Complex.besselJ ν (x : ℂ) - Complex.besselJ (ν+1) (x : ℂ)) x := by
  let b := (x : ℂ)/2
  let w := -b^2
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hb : b ≠ 0 := div_ne_zero hxC (by norm_num)
  have hSlit : b ∈ Complex.slitPlane := by
    change (x : ℂ)/2 ∈ Complex.slitPlane
    rw [show (x : ℂ)/2 = ((x/2 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_mem_slitPlane.mpr (half_pos hx)
  have hHalf : HasDerivAt (fun y : ℂ => y/2) (1/2) (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).div_const 2
  have hArg : HasDerivAt (fun y : ℂ => -(y/2)^2) (-b) (x : ℂ) := by
    convert (hHalf.pow 2).neg using 1
    dsimp only [b]
    norm_num <;> ring
  have hF := (spectral_regularizedBessel_hasDerivAt (ν+1) w).comp (x : ℂ) hArg
  have hD := ((hHalf.cpow_const (c := ν) hSlit).mul hF).comp_ofReal
  change HasDerivAt (fun y : ℝ => ((y : ℂ)/2)^ν*F(ν+1) (-((y : ℂ)/2)^2)) _ x
  convert hD using 1
  · funext y
    rfl
  · change (ν/(x : ℂ))*(b^ν*F(ν+1) w) - b^(ν+1)*F(ν+1+1) w =
      ν*b^(ν-1)*(1/2)*F(ν+1) w + b^ν*(F(ν+1+1) w*(-b))
    rw [Complex.cpow_add ν 1 hb, Complex.cpow_one, Complex.cpow_sub ν 1 hb, Complex.cpow_one]
    dsimp only [b]
    field_simp [hxC] <;> ring

theorem spectral_besselJ_spatial_ode (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    let J : ℝ → ℂ := fun y => Complex.besselJ ν (y : ℂ)
    (x : ℂ)^2*deriv (deriv J) x + (x : ℂ)*deriv J x + (x : ℂ)^2*J x = ν^2*J x := by
  dsimp only
  let J (y : ℝ) := Complex.besselJ ν (y : ℂ)
  let J₁ (y : ℝ) := Complex.besselJ (ν+1) (y : ℂ)
  let J₂ (y : ℝ) := Complex.besselJ (ν+2) (y : ℂ)
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hD : HasDerivAt J ((ν/(x : ℂ))*J x - J₁ x) x := spectral_besselJ_spatial_hasDerivAt ν hx
  have hD₁ : HasDerivAt J₁ (((ν+1)/(x : ℂ))*J₁ x - J₂ x) x := by
    simpa only [J₁,J₂,show ν+1+1 = ν+2 by ring] using spectral_besselJ_spatial_hasDerivAt (ν+1) hx
  have hFrac : HasDerivAt (fun y : ℝ => ν/(y : ℂ)) (-ν/(x : ℂ)^2) x := by
    have h : HasDerivAt (fun y : ℂ => ν/y) (-ν/(x : ℂ)^2) (x : ℂ) := by
      convert (hasDerivAt_const (x : ℂ) ν).div (hasDerivAt_id (x : ℂ)) hxC using 1
      · funext y
        rfl
      · simp
    exact h.comp_ofReal
  have hD₂ : HasDerivAt (deriv J)
      ((-ν/(x : ℂ)^2)*J x + (ν/(x : ℂ))*((ν/(x : ℂ))*J x - J₁ x) -
        (((ν+1)/(x : ℂ))*J₁ x - J₂ x)) x :=
    ((hFrac.mul hD).sub hD₁).congr_of_eventuallyEq (by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (spectral_besselJ_spatial_hasDerivAt ν hy).deriv)
  change (x : ℂ)^2*deriv (deriv J) x + (x : ℂ)*deriv J x + (x : ℂ)^2*J x = ν^2*J x
  rw [hD₂.deriv,hD.deriv]
  calc
    _ = ν^2*J x + (x : ℂ)^2*(J x + J₂ x - (2*(ν+1)/(x : ℂ))*J₁ x) := by
      field_simp [hxC] <;> ring
    _ = _ := by
      have hR : J x = (2*(ν+1)/(x : ℂ))*J₁ x - J₂ x :=
        spectral_besselJ_order_recurrence ν hx
      rw [hR]
      ring

end ArtinMatthews
