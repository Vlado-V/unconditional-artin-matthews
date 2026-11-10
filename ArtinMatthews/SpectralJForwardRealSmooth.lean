module

public import ArtinMatthews.SpectralJForwardWeylNormalization
public import ArtinMatthews.SpectralJForwardHolomorphic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The literal forward transform and its hyperbolic spectral weight are
smooth on the real axis. Only the real-axis nonvanishing of cosh is used. -/
noncomputable section
open Set Complex
open scoped ContDiff

namespace ArtinMatthews

theorem spectralJForwardTransform_real_contDiff (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralJForwardTransform f (t : ℂ)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have ha : AnalyticAt ℂ (spectralJForwardTransform f) (t : ℂ) :=
    spectralJForwardTransform_analyticOnNhd f hf hc hp _ (by simp)
  have h : ContDiffAt ℂ ∞ (spectralJForwardTransform f) (t : ℂ) := ha.contDiffAt
  exact (h.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt

theorem spectralJForwardSpectralWeight_real_contDiff (f : ℝ → ℂ) (hf : Continuous f)
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ)) :
    ContDiff ℝ ∞ (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ)) := by
  have hDen : ContDiff ℝ ∞ (fun t : ℝ => Real.cosh (Real.pi*t)) :=
    Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  have hPref : ContDiff ℝ ∞ (fun t : ℝ => ((Real.pi/Real.cosh (Real.pi*t) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.div hDen (fun t => (Real.cosh_pos _).ne'))
  have he : (fun t : ℝ => spectralJForwardSpectralWeight f (t : ℂ)) =
      fun t : ℝ => ((Real.pi/Real.cosh (Real.pi*t) : ℝ) : ℂ)*spectralJForwardTransform f (t : ℂ) := by
    funext t
    rw [spectralJForwardSpectralWeight, ← Complex.ofReal_mul, ← Complex.ofReal_cosh, Complex.ofReal_div]
  rw [he]
  exact hPref.mul (spectralJForwardTransform_real_contDiff f hf hc hp)

end ArtinMatthews
