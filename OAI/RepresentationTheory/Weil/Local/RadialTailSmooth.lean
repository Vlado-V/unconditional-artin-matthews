module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.RadialTailCutoffBound
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

/-! # Radial Tail Smooth -/

namespace OAI.RepresentationTheory.Weil.Local.RadialTailSmooth.Construction

noncomputable section

/-! Smoothness of the radial tail weight across its zero neighborhood. -/

open Filter Set
open scoped _root_.Topology ContDiff

theorem radialCutoff_contDiff (R : ℝ) : ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialCutoff R) :=
  RadialTailCutoffBound.Construction.radialCutoffBase_contDiff.comp (contDiff_id.div_const R)

theorem radialTailWeight_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeight s ε R) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : 0 < t
  · have hp : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ s) t := Real.contDiffAt_rpow_const_of_ne ht.ne'
    have he : ContDiffAt ℝ ∞ (fun x : ℝ => Real.exp (-ε * x ^ s)) t :=
      Real.contDiff_exp.contDiffAt.comp t (contDiffAt_const.mul hp)
    have hw : ContDiffAt ℝ ∞ (RealPower.Construction.realPowerWeight s ε) t := he.div contDiffAt_id ht.ne'
    exact (radialCutoff_contDiff R).contDiffAt.mul hw
  · have htR : t < R := (le_of_not_gt ht).trans_lt hR
    have heq : RadialTailCutoffBound.Construction.radialTailWeight s ε R =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds htR] with x hx
      exact RadialTailCutoffBound.Construction.radialTailWeight_zero s ε R x hR hx
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem radialTailWeight_deriv (s ε R : ℝ) (hR : 0 < R) :
    deriv (RadialTailCutoffBound.Construction.radialTailWeight s ε R) = RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R :=
  funext fun t => (RadialTailCutoffBound.Construction.radialTailWeight_hasDerivAt s ε R hR t).deriv

theorem radialTailWeight_second_deriv (s ε R : ℝ) (hR : 0 < R) :
    deriv (deriv (RadialTailCutoffBound.Construction.radialTailWeight s ε R)) = RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R := by
  rw [radialTailWeight_deriv s ε R hR]
  exact funext fun t => (RadialTailCutoffBound.Construction.radialTailWeightDerivative_hasDerivAt s ε R hR t).deriv

theorem radialTailWeightDerivative_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeightDerivative s ε R) := by
  rw [← radialTailWeight_deriv s ε R hR]
  exact (radialTailWeight_contDiff s ε R hR).iterate_deriv 1

theorem radialTailWeightSecondDerivative_contDiff (s ε R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (RadialTailCutoffBound.Construction.radialTailWeightSecondDerivative s ε R) := by
  rw [← radialTailWeight_second_deriv s ε R hR]
  exact (radialTailWeight_contDiff s ε R hR).iterate_deriv 2

end

end OAI.RepresentationTheory.Weil.Local.RadialTailSmooth.Construction
