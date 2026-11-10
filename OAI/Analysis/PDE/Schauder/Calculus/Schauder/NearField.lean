module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Singular
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.RadialIntegral
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


set_option backward.privateInPublic true
@[expose] public section

/-! The quantitative near-field estimate for the Newtonian Hessian singular integral. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem integrableOn_compensatedNewtonianEntry (f : E → ℝ) (x v w : E)
    (hd : 1 ≤ Module.finrank ℝ E) (hf : Measurable f) {H α : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (μ : Measure E) [μ.IsAddHaarMeasure] (R : ℝ) :
    IntegrableOn (compensatedNewtonianEntry f x v w) (ball 0 R) μ :=
  ((locallyIntegrable_compensatedNewtonianEntry f x v w hd hf hH hα hholder μ).integrableOn_isCompact
    (isCompact_closedBall 0 R)).mono_set ball_subset_closedBall

theorem compensatedNewtonian_nearField_bound (f : E → ℝ) (x v w : E)
    (hd : 1 ≤ Module.finrank ℝ E) {H α R : ℝ}
    (hH : 0 ≤ H) (hα : 0 < α) (hR : 0 < R)
    (hholder : ∀ y, |f (x - y) - f x| ≤ H * ‖y‖ ^ α)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    |∫ y in ball (0 : E) R, compensatedNewtonianEntry f x v w y ∂μ| ≤
      H * newtonianSizeConstant (Module.finrank ℝ E) * rieszBallMass μ α *
        R ^ α * ‖v‖ * ‖w‖ := by
  let : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hg := (integrableOn_riesz_majorant μ hd hα R).const_mul
    (H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖)
  have hb : ∀ᵐ y ∂μ.restrict (ball (0 : E) R),
      ‖compensatedNewtonianEntry f x v w y‖ ≤
        (H * newtonianSizeConstant (Module.finrank ℝ E) * ‖v‖ * ‖w‖) *
          ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) := by
    have hzero : ∀ᵐ y ∂μ, y ≠ (0 : E) := by rw [ae_iff]; simp
    filter_upwards [ae_restrict_of_ae hzero] with y hy
    exact compensatedNewtonianEntry_bound f x v w hH hholder hy
  have hi := norm_integral_le_of_norm_le hg hb
  rw [integral_const_mul, integral_riesz_majorant_ball μ α hR] at hi
  rw [Real.norm_eq_abs] at hi
  convert hi using 1 ; ring

end OAI.Analysis.PDE.Schauder
