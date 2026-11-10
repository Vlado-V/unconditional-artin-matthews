module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd


set_option backward.privateInPublic true
@[expose] public section

/-! Exact scaling of the integrable radial majorants used in the Schauder estimates. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped Pointwise
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rieszBallMass (μ : Measure E) (α : ℝ) : ℝ :=
  ∫ y in ball (0 : E) 1, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) ∂μ

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem rieszBallMass_nonneg (μ : Measure E) (α : ℝ) : 0 ≤ rieszBallMass μ α :=
  integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg y) _

theorem integrableOn_riesz_majorant (μ : Measure E) [μ.IsAddHaarMeasure]
    (hd : 1 ≤ Module.finrank ℝ E) {α : ℝ} (hα : 0 < α) (R : ℝ) :
    IntegrableOn (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball 0 R) μ := by
  apply integrableOn_ball_of_norm_le_rpow hd (C := 1)
    (α := (Module.finrank ℝ E : ℝ) - α) (by linarith)
  · filter_upwards with y
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg y) _),
      neg_sub, one_mul]
    exact le_rfl
  · exact (by fun_prop : Measurable (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)))).aestronglyMeasurable

theorem integral_riesz_majorant_ball (μ : Measure E) [μ.IsAddHaarMeasure]
    (α : ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ y in ball (0 : E) R, ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) ∂μ) =
      R ^ α * rieszBallMass μ α := by
  have he := μ.setIntegral_comp_smul_of_pos
    (fun y : E => ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ))) (ball (0 : E) 1) hR
  have himage : R • ball (0 : E) 1 = ball 0 R := by
    rw [_root_.smul_ball hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one]
  have hf (y : E) : ‖R • y‖ ^ (α - (Module.finrank ℝ E : ℝ)) =
      R ^ (α - (Module.finrank ℝ E : ℝ)) * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.mul_rpow hR.le (norm_nonneg y)]
  simp only [himage, hf, integral_const_mul, smul_eq_mul] at he
  have hp : R ^ Module.finrank ℝ E * R ^ (α - (Module.finrank ℝ E : ℝ)) = R ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  have hh := congrArg (fun t : ℝ => R ^ Module.finrank ℝ E * t) he
  rw [← mul_assoc, hp, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul] at hh
  exact hh.symm

end OAI.Analysis.PDE.Schauder
