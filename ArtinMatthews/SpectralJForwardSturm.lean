module

public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralBesselJSpatialODE
public import ArtinMatthews.SourceSturmSpectralPowers


set_option backward.privateInPublic true
@[expose] public section

/-! The literal nonzero-parameter forward J kernel is a smooth eigenfunction
of the compact dx/x Sturm operator. -/
noncomputable section
open Set Filter Complex
open scoped Topology ContDiff

namespace ArtinMatthews
open SourceSturm

private theorem spectral_besselJ_spatial_contDiffAt (ν : ℂ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ 2 (fun y : ℝ => Complex.besselJ ν (y : ℂ)) x := by
  have ha : AnalyticAt ℂ (Complex.besselJ ν) (x : ℂ) :=
    Complex.analyticAt_besselJ ν (Complex.ofReal_mem_slitPlane.mpr hx)
  have h : ContDiffAt ℂ 2 (Complex.besselJ ν) (x : ℂ) := ha.contDiffAt
  exact (h.restrict_scalars ℝ).comp x Complex.ofRealCLM.contDiff.contDiffAt

theorem spectralJForwardKernel_spatial_contDiffOn {z : ℂ} (hz : z ≠ 0) :
    ContDiffOn ℝ 2 (spectralJForwardKernel z) (Ioi (0 : ℝ)) := by
  have hEq : spectralJForwardKernel z = fun x : ℝ =>
      (Complex.besselJ (-2*I*z) (x : ℂ)-Complex.besselJ (2*I*z) (x : ℂ))/
        (2*Complex.sin ((Real.pi : ℂ)*I*z)) := funext (spectralJForwardKernel_of_ne_zero hz)
  rw [hEq]
  have h₁ : ContDiffOn ℝ 2 (fun x : ℝ => Complex.besselJ (-2*I*z) (x : ℂ)) (Ioi (0 : ℝ)) :=
    fun x hx => (spectral_besselJ_spatial_contDiffAt (-2*I*z) hx).contDiffWithinAt
  have h₂ : ContDiffOn ℝ 2 (fun x : ℝ => Complex.besselJ (2*I*z) (x : ℂ)) (Ioi (0 : ℝ)) :=
    fun x hx => (spectral_besselJ_spatial_contDiffAt (2*I*z) hx).contDiffWithinAt
  exact (h₁.sub h₂).div_const _

theorem spectralJForwardKernel_sturm_eigen {z : ℂ} (hz : z ≠ 0) (x : ℝ) (hx : 0 < x) :
    sturmD (spectralJForwardKernel z) x = (-4 : ℂ)*z^2*spectralJForwardKernel z x := by
  let J₁ (y : ℝ) := Complex.besselJ (-2*I*z) (y : ℂ)
  let J₂ (y : ℝ) := Complex.besselJ (2*I*z) (y : ℂ)
  let c := 2*Complex.sin ((Real.pi : ℂ)*I*z)
  have hEq : spectralJForwardKernel z = fun y => (J₁ y-J₂ y)/c :=
    funext (spectralJForwardKernel_of_ne_zero hz)
  have h₁ (y : ℝ) (hy : 0 < y) : ContDiffAt ℝ 2 J₁ y :=
    spectral_besselJ_spatial_contDiffAt (-2*I*z) hy
  have h₂ (y : ℝ) (hy : 0 < y) : ContDiffAt ℝ 2 J₂ y :=
    spectral_besselJ_spatial_contDiffAt (2*I*z) hy
  have hd (y : ℝ) (hy : 0 < y) :
      deriv (spectralJForwardKernel z) y = (deriv J₁ y-deriv J₂ y)/c := by
    rw [hEq]
    exact ((((h₁ y hy).differentiableAt (by norm_num)).hasDerivAt.sub
      ((h₂ y hy).differentiableAt (by norm_num)).hasDerivAt).div_const c).deriv
  have hd₁ := ((h₁ x hx).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd₂ := ((h₂ x hx).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdd : deriv (deriv (spectralJForwardKernel z)) x =
      (deriv (deriv J₁) x-deriv (deriv J₂) x)/c := by
    apply (((hd₁.hasDerivAt.sub hd₂.hasDerivAt).div_const c).congr_of_eventuallyEq ?_).deriv
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact hd y hy
  have hD₁ : sturmD J₁ x = (-2*I*z)^2*J₁ x := spectral_besselJ_spatial_ode (-2*I*z) hx
  have hD₂ : sturmD J₂ x = (2*I*z)^2*J₂ x := spectral_besselJ_spatial_ode (2*I*z) hx
  calc
    _ = (sturmD J₁ x - sturmD J₂ x)/c := by
      unfold sturmD
      rw [hdd, hd x hx, congrFun hEq x]
      ring
    _ = _ := by
      rw [hD₁,hD₂,congrFun hEq x,
        show (-2*I*z)^2 = (-4 : ℂ)*z^2 by rw [mul_pow,mul_pow,I_sq]; ring,
        show (2*I*z)^2 = (-4 : ℂ)*z^2 by rw [mul_pow,mul_pow,I_sq]; ring]
      ring

end ArtinMatthews
