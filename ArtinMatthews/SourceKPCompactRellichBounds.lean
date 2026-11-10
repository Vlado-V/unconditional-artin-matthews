module

public import ArtinMatthews.SourceKPCompactFormCoreNorm
public import ArtinMatthews.SourceHyperbolicH1Gradient
public import ArtinMatthews.SourceKPCompactCoreLocalization
public import ArtinMatthews.H1LocalUniformBounds
public import ArtinMatthews.SourceKPCompactCoreLocalizationBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! A fixed chart plateau localizes a bounded automorphic core family to bounded native H1 tests. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "T" => SourceKPCompactFormCore K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)

theorem sourceKPCompactRellichBounds (b : SourceKPFiniteLevelFiber K hζ)
    (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) (r : ℝ) :
    ∃ A B : ℝ, ∀ f ∈ Metric.closedBall (0 : T) r,
      ‖h1TestMass (sourceKPCompactCoreLocalized K hζ f.val b p η).val‖ ^ 2 ≤ A ∧
      ‖h1TestGradient (sourceKPCompactCoreLocalized K hζ f.val b p η).val‖ ^ 2 ≤ B := by
  let H := SourceKPFiniteChartStabilizer K hζ b p
  obtain ⟨M, B, _, hB, hη, hEη⟩ := h1LocalTest_uniform_bounds _ η
  refine ⟨(Nat.card H : ℝ) * M ^ 2 * r ^ 2,
    2 * (Nat.card H : ℝ) * (M ^ 2 * r ^ 2 + B * r ^ 2), ?_⟩
  intro f hf
  have hnr : ‖f‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hf
  have hf2 := pow_le_pow_left₀ (norm_nonneg f) hnr 2
  have hnorm := sourceKPCompactFormCore_norm_sq K hζ f
  change ‖f‖ ^ 2 = ‖sourceKPCompactCoreMass K hζ 2 f.val‖ ^ 2 +
    ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ at hnorm
  have hE : 0 ≤ ∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ :=
    integral_nonneg (sourceKPCompactCoreEnergy_nonneg K hζ f.val)
  have hm : ‖sourceKPCompactCoreMass K hζ 2 f.val‖ ^ 2 ≤ r ^ 2 := by linarith
  have hg : (∫ y, sourceKPCompactCoreEnergy K hζ f.val y ∂μ) ≤ r ^ 2 := by
    linarith [sq_nonneg ‖sourceKPCompactCoreMass K hζ 2 f.val‖]
  constructor
  · exact (sourceKPCompactCoreLocalized_mass_bound K hζ f.val b p η M
      (fun x _ => hη x)).trans (mul_le_mul_of_nonneg_left hm (by positivity))
  · exact (sourceKPCompactCoreLocalized_gradient_bound K hζ f.val b p η M B
      (fun x _ => hη x) (fun x _ => hEη x)).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hg (sq_nonneg M))
          (mul_le_mul_of_nonneg_left hm hB)) (by positivity))

theorem sourceKPCompactCoreLocalized_support_subset (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) :
    tsupport (sourceKPCompactCoreLocalized K hζ f b p η).val.val ⊆ tsupport η.val.val := by
  have he : (sourceKPCompactCoreLocalized K hζ f b p η).val.val =
      η.val.val * sourceKPCompactChartPullback K hζ f.val b :=
    funext (sourceKPCompactCoreLocalized_apply K hζ f b p η)
  rw [he]
  exact tsupport_mul_subset_left

end
end ArtinMatthews
