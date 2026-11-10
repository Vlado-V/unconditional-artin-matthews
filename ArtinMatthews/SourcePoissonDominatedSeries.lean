module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open MeasureTheory
noncomputable section

/-- The same summable row majorant controls the absolute integral of the
joint series and the sum of the absolute integrals. -/
theorem sourcePoisson_mul_tsum_integrable_and_summable
    {α ι : Type} [MeasurableSpace α] [Countable ι] {μ : Measure α}
    (K : α → ℂ) (hK : Integrable K μ) (A : ι → α → ℂ)
    (hA : ∀ i, Measurable (A i)) (B : ι → ℝ) (hB : Summable B)
    (hbound : ∀ i p, ‖A i p‖ ≤ B i) :
    Integrable (fun p => K p * (∑' i, A i p)) μ ∧
      Summable (fun i => ∫ p, ‖K p * A i p‖ ∂μ) := by
  have hnorm (p : α) : Summable (fun i => ‖A i p‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => hbound i p) hB
  refine ⟨(hK.norm.mul_const (∑' i, B i)).mono'
    (hK.aestronglyMeasurable.mul (Measurable.tsum hA).aestronglyMeasurable) ?_, ?_⟩
  · filter_upwards with p
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_tsum_le_tsum_norm (hnorm p)).trans
      ((hnorm p).tsum_le_tsum (fun i => hbound i p) hB)
  · have hNonnegInt (i : ι) : 0 ≤ ∫ p, ‖K p * A i p‖ ∂μ :=
      integral_nonneg (fun p => norm_nonneg (K p * A i p))
    refine Summable.of_nonneg_of_le hNonnegInt ?_
      (hB.mul_left (∫ p, ‖K p‖ ∂μ))
    intro i
    rw [← integral_mul_const]
    have hNonneg : ∀ᵐ p ∂μ, 0 ≤ ‖K p * A i p‖ :=
      Filter.Eventually.of_forall (fun p => norm_nonneg (K p * A i p))
    refine integral_mono_of_nonneg hNonneg (hK.norm.mul_const (B i)) ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound i p) (norm_nonneg _)

end
end ArtinMatthews.SourcePhysical
