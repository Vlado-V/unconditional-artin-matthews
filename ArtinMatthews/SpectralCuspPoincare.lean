module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.Conductivity.Variational.IntervalMeanPoincare


set_option backward.privateInPublic true
@[expose] public section

/-!
The horizontal mean-zero inequality needed for compactness in an H² cusp.
The real interval theorem is reused verbatim from math-main.  This file extends
it to actual complex sections, with the derivative and mean taken on the
section itself.  No spectral estimate or eigenfunction expansion is assumed.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace ArtinMatthews

/-- A complex horizontal section with zero constant term has its mass controlled
by its actual horizontal derivative.  Periodicity is unnecessary for this
inequality; the zero mean is the substantive cusp condition. -/
theorem cusp_section_poincare {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {a b : ℝ} (hab : a < b) (hmean : (∫ x in a..b, f x) = 0) :
    (∫ x in a..b, ‖f x‖ ^ 2) ≤
      (b - a) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  have hre : ContDiff ℝ ∞ (fun x => (f x).re) := Complex.reCLM.contDiff.comp hf
  have him : ContDiff ℝ ∞ (fun x => (f x).im) := Complex.imCLM.contDiff.comp hf
  have hmr : (∫ x in a..b, (f x).re) = 0 := by
    change (∫ x in a..b, Complex.reCLM (f x)) = 0
    rw [Complex.reCLM.intervalIntegral_comp_comm (hf.continuous.intervalIntegrable a b),
      hmean]
    rfl
  have hmi : (∫ x in a..b, (f x).im) = 0 := by
    change (∫ x in a..b, Complex.imCLM (f x)) = 0
    rw [Complex.imCLM.intervalIntegral_comp_comm (hf.continuous.intervalIntegrable a b),
      hmean]
    rfl
  have hdr (x : ℝ) : deriv (fun x => (f x).re) x = (deriv f x).re :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
      ((hf.differentiable (by simp)) x).hasDerivAt).deriv
  have hdi (x : ℝ) : deriv (fun x => (f x).im) x = (deriv f x).im :=
    (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x
      ((hf.differentiable (by simp)) x).hasDerivAt).deriv
  have hr := OAI.ScalarConductivity.smooth_interval_mean_poincare hre hab
  have hi := OAI.ScalarConductivity.smooth_interval_mean_poincare him hab
  simp only [hmr, hmi, zero_div, sub_zero, hdr, hdi] at hr hi
  have hs (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp_rw [hs]
  have hd := hf.continuous_deriv (by simp)
  rw [intervalIntegral.integral_add (f := fun x => (f x).re ^ 2)
    (g := fun x => (f x).im ^ 2)
    ((Complex.continuous_re.comp hf.continuous).pow 2 |>.intervalIntegrable a b)
    ((Complex.continuous_im.comp hf.continuous).pow 2 |>.intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun x => (deriv f x).re ^ 2)
    (g := fun x => (deriv f x).im ^ 2)
    ((Complex.continuous_re.comp hd).pow 2 |>.intervalIntegrable a b)
    ((Complex.continuous_im.comp hd).pow 2 |>.intervalIntegrable a b), mul_add]
  exact add_le_add hr hi

end ArtinMatthews
