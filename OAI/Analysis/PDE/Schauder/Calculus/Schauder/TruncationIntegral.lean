module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TailIntegral
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.Analysis.PDE.Schauder.Calculus.Schauder.TruncationBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The weighted L¹ derivative bound for smooth far-field kernels. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem truncatedNewtonianEntry_weighted_fderiv (v w : E) :
    ∃ C > 0, ∀ (r α : ℝ) (μ : Measure E), μ.IsAddHaarMeasure →
      1 ≤ Module.finrank ℝ E → 0 < r → α < 1 →
      Integrable (fun y => ‖fderiv ℝ (truncatedNewtonianEntry (Module.finrank ℝ E) v w r) y‖ * ‖y‖ ^ α) μ ∧
      (∫ y, ‖fderiv ℝ (truncatedNewtonianEntry (Module.finrank ℝ E) v w r) y‖ * ‖y‖ ^ α ∂μ) ≤
        C * (r / 2) ^ (α - 1) * rieszTailMass μ α := by
  obtain ⟨C, hC, hbound⟩ := truncatedNewtonianEntry_fderiv_bound (Module.finrank ℝ E) v w
  refine ⟨C, hC, ?_⟩
  intro r α μ hμ hd hr hα
  let := hμ
  let S : Set E := {y | r / 2 < ‖y‖}
  have hS : MeasurableSet S := measurableSet_lt measurable_const continuous_norm.measurable
  let M : E → ℝ := S.indicator (fun y => C * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1))
  have hM : Integrable M μ := by
    exact (integrable_indicator_iff hS).mpr
      ((integrableOn_riesz_tail μ hd hα (by positivity : 0 < r / 2)).const_mul C)
  let F : E → ℝ := fun y => ‖fderiv ℝ (truncatedNewtonianEntry (Module.finrank ℝ E) v w r) y‖ * ‖y‖ ^ α
  have hFmeas : Measurable F := by
    dsimp [F]
    fun_prop
  have hFpos (y : E) : 0 ≤ F y := by dsimp [F]; positivity
  have hFM (y : E) : F y ≤ M y := by
    by_cases hy : y ∈ S
    · have hn : 0 < ‖y‖ := lt_trans (by positivity : 0 < r / 2) hy
      have hy0 := norm_pos_iff.mp hn
      simp only [M, Set.indicator_of_mem hy]
      calc
        F y ≤ (C * ‖y‖ ^ (-(Module.finrank ℝ E : ℝ) - 1)) * ‖y‖ ^ α :=
          mul_le_mul_of_nonneg_right (hbound r hr y hy0) (Real.rpow_nonneg (norm_nonneg _) _)
        _ = _ := by
          rw [show α - (Module.finrank ℝ E : ℝ) - 1 = (-(Module.finrank ℝ E : ℝ) - 1) + α by ring,
            Real.rpow_add hn]
          ring
    · have hn : ‖y‖ < r := by
        have : ‖y‖ ≤ r / 2 := le_of_not_gt hy
        linarith
      simp [F, M, hy, truncatedNewtonianEntry_fderiv_zero _ v w hr hn]
  have hi : Integrable F μ := hM.mono' hFmeas.aestronglyMeasurable (by
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hFpos y)] using hFM y)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ y, M y ∂μ := integral_mono_ae hi hM (Filter.Eventually.of_forall hFM)
    _ = _ := by
      rw [show M = S.indicator (fun y => C * ‖y‖ ^ (α - (Module.finrank ℝ E : ℝ) - 1)) from rfl,
        integral_indicator hS, integral_const_mul, integral_riesz_tail μ α (by positivity : 0 < r / 2)]
      ring

end OAI.Analysis.PDE.Schauder
