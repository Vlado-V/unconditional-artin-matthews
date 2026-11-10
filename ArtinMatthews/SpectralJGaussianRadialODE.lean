module

public import ArtinMatthews.SpectralJGaussianKernel
public import ArtinMatthews.SpectralJFactorialDerivatives
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

/-! The actual Gaussian Bessel kernel satisfies the radial divergence equation. -/

namespace ArtinMatthews
noncomputable section

private def radialArgument (w x : ℝ) : ℝ := -(w / 8) * x ^ 2

private theorem radialArgument_hasDerivAt (w x : ℝ) :
    HasDerivAt (radialArgument w) (-(w / 4) * x) x := by
  change HasDerivAt (fun q : ℝ => -(w / 8) * q ^ 2) (-(w / 4) * x) x
  have h := ((hasDerivAt_id' x).fun_pow 2).const_mul (-(w / 8))
  convert h using 1 <;> norm_num <;> ring

private theorem factorial_radial_hasDerivAt (w : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun q : ℝ => spectralJFactorialSeries j (radialArgument w q : ℂ))
      (((-(w / 4) * x : ℝ) : ℂ) * spectralJFactorialSeries (j + 1) (radialArgument w x : ℂ)) x := by
  have h := (spectralJFactorialSeries_hasDerivAt j (radialArgument w x : ℂ)).comp_ofReal
  simpa only [Function.comp_def, Complex.real_smul] using
    h.scomp x (radialArgument_hasDerivAt w x)

private theorem gaussianKernel_eq_factorial_radial (w x : ℝ) (hw : 0 ≤ w) :
    spectralJGaussianKernel x w = spectralJFactorialSeries 0 (radialArgument w x : ℂ) := by
  rw [show radialArgument w x = -((x ^ 2 / 8) * w) by unfold radialArgument; ring,
    Complex.ofReal_neg]
  exact (spectralJFactorialSeries_zero_eq_besselJ _ (by positivity)).symm

private theorem gaussianKernel_hasDerivAt (w x : ℝ) (hw : 0 ≤ w) :
    HasDerivAt (fun q : ℝ => spectralJGaussianKernel q w)
      (((-(w / 4) * x : ℝ) : ℂ) * spectralJFactorialSeries 1 (radialArgument w x : ℂ)) x := by
  simp_rw [gaussianKernel_eq_factorial_radial w _ hw]
  exact factorial_radial_hasDerivAt w 0 x

theorem spectralJGaussianKernel_differentiable (w : ℝ) (hw : 0 ≤ w) :
    Differentiable ℝ (fun x : ℝ => spectralJGaussianKernel x w) :=
  fun x => (gaussianKernel_hasDerivAt w x hw).differentiableAt

theorem spectralJGaussianKernel_deriv_continuous (w : ℝ) (hw : 0 ≤ w) :
    Continuous (deriv (fun x : ℝ => spectralJGaussianKernel x w)) := by
  have he : deriv (fun x : ℝ => spectralJGaussianKernel x w) =
      fun x => (((-(w / 4) * x : ℝ) : ℂ) * spectralJFactorialSeries 1 (radialArgument w x : ℂ)) := by
    funext x
    exact (gaussianKernel_hasDerivAt w x hw).deriv
  rw [he]
  have hc : Continuous (fun x : ℝ => ((-(w / 4) * x : ℝ) : ℂ)) := by fun_prop
  have hU : Continuous (fun x : ℝ => spectralJFactorialSeries 1 (radialArgument w x : ℂ)) :=
    continuous_iff_continuousAt.mpr fun x => (factorial_radial_hasDerivAt w 1 x).continuousAt
  exact hc.mul hU

/-- The divergence form of the order-zero equation, with frequency
(w/2) for the literal square-root argument. -/
theorem spectralJGaussianKernel_radial_ode (w x : ℝ) (hw : 0 ≤ w) :
    HasDerivAt (fun q : ℝ => (q : ℂ) * deriv (fun y => spectralJGaussianKernel y w) q)
      (-(w : ℂ) / 2 * (x : ℂ) * spectralJGaussianKernel x w) x := by
  let p := fun q : ℝ => -(w / 4) * q ^ 2
  have hp : HasDerivAt p (-(w / 2) * x) x := by
    have h := ((hasDerivAt_id' x).fun_pow 2).const_mul (-(w / 4))
    convert h using 1
    simp only [Nat.reduceSub, pow_one, mul_one]
    push_cast
    ring
  have he : (fun q : ℝ => (q : ℂ) * deriv (fun y => spectralJGaussianKernel y w) q) =
      fun q : ℝ => (p q : ℂ) * spectralJFactorialSeries 1 (radialArgument w q : ℂ) := by
    funext q
    rw [(gaussianKernel_hasDerivAt w q hw).deriv]
    dsimp only [p]
    push_cast
    ring
  rw [he]
  have h := (hp.ofReal_comp).mul (factorial_radial_hasDerivAt w 1 x)
  convert h using 1
  rw [gaussianKernel_eq_factorial_radial w x hw, ← spectralJFactorialSeries_ode]
  dsimp only [p, radialArgument]
  push_cast
  ring

end
end ArtinMatthews
