module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Green.Cutoff
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Dominated-convergence statements for the defining-function cutoffs. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {S : Set E}

theorem integral_boundaryCutoff_tendsto {r f : E → ℝ}
    (hr : Continuous r) (hf : Continuous f) (hfi : IntegrableOn f S μ)
    (hneg : ∀ x ∈ S, r x < 0) (hS : MeasurableSet S) :
    Tendsto (fun k : ℕ ↦ ∫ x in S, boundaryCutoff (r x) k * f x ∂μ)
      atTop (𝓝 (∫ x in S, f x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
  · intro k
    exact ((Real.smoothTransition.continuous.comp (continuous_const.mul hr)).mul hf).aestronglyMeasurable
  · exact hfi.norm
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    have hc : ‖boundaryCutoff (r x) k‖ ≤ 1 := by
      unfold boundaryCutoff
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (f x))
  · filter_upwards [ae_restrict_mem hS] with x hx
    simpa only [one_mul] using (boundaryCutoff_tendsto (hneg x hx)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ f x) atTop (𝓝 (f x)))

theorem integral_transitionSlope_tendsto_zero {r b : E → ℝ}
    (hr : Continuous r) (hbi : IntegrableOn b S μ) :
    Tendsto (fun k : ℕ ↦ ∫ x in S, transitionSlope (-((k : ℝ) + 1) * r x) * b x ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := exists_transitionSlope_bound
  have h := tendsto_integral_of_dominated_convergence (μ := μ.restrict S)
    (F := fun k x ↦ transitionSlope (-((k : ℝ) + 1) * r x) * b x)
    (f := fun _ ↦ (0 : ℝ)) (fun x ↦ C * ‖b x‖) ?_ ?_ ?_ ?_
  · simpa only [integral_zero] using h
  · intro k
    exact (continuous_transitionSlope.comp (continuous_const.mul hr)).aestronglyMeasurable.mul
      hbi.aestronglyMeasurable
  · exact hbi.norm.const_mul C
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg (b x))
  · apply Filter.Eventually.of_forall
    intro x
    simpa only [zero_mul] using (transitionSlope_cutoff_tendsto (r x)).mul
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ b x) atTop (𝓝 (b x)))

end OAI.Analysis.PDE.Green
