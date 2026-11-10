module

public import ArtinMatthews.SpectralCuspUnitFourierMean
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Continuous dependence of the literal unit-width Fourier mean on
positive height. The averaging interval is fixed before integration. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0UnitCuspFourierMean_continuousOn (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    ContinuousOn (gamma0UnitCuspFourierMean N r m F) (Ioi (0 : ℝ)) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let H (p : Ioi (0 : ℝ) × ℝ) : UpperHalfPlane :=
    gamma0EisensteinHorizontalPoint p.1.val p.1.property p.2
  have hH : Continuous H := by
    have hc : Continuous (fun p : Ioi (0 : ℝ) × ℝ => Complex.mk p.2 p.1.val) := by
      convert Complex.continuous_ofReal.comp continuous_snd |>.add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul_const Complex.I) using 1
      funext p
      apply Complex.ext <;> simp
    exact hc.upperHalfPlaneMk (fun p => p.1.property)
  let U (y : Ioi (0 : ℝ)) (x : ℝ) :=
    cuspFourierPhase 1 m x * F (gamma0TrueCuspScaling N r • H (y,x))
  have hU : Continuous U.uncurry :=
    ((cuspFourierPhase_contDiff 1 m).continuous.comp continuous_snd).mul
      (hF.comp ((continuous_const_smul (gamma0TrueCuspScaling N r)).comp hH))
  have h : Continuous (fun y : Ioi (0 : ℝ) => ∫ x in (0 : ℝ)..1, U y x) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hU 0 1
  convert h using 1
  funext y
  exact dite_eq_left y.property

theorem gamma0UnitCuspFourierMean_raw_continuousOn (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m : ℤ) (F : UpperHalfPlane → ℂ) (hF : Continuous F) :
    ContinuousOn (fun y => gamma0UnitCuspFourierMean N r m F
      (y/(gamma0CuspTrueWidth N r : ℝ))) (Ioi (0 : ℝ)) := by
  exact (gamma0UnitCuspFourierMean_continuousOn N r m F hF).comp
    (continuous_id.div_const _).continuousOn
    (fun y hy => show 0 < y/(gamma0CuspTrueWidth N r : ℝ) from
      div_pos (show 0 < y from hy) (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)))

end ArtinMatthews

