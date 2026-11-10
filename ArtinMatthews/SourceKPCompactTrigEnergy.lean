module

public import ArtinMatthews.SourceKPCompactTrigCutoff
public import ArtinMatthews.SourceKPCompactExhaustionCore
public import ArtinMatthews.SourceHyperbolicTrigPartition
public import ArtinMatthews.SourceKPCompactCoreGradient
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

/-! Exact quotient energy of the two genuine trigonometric cutoffs. -/
namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "T" => sourceKPCompactC2Core K hζ
local notation "Ω" => productUpper (InfinitePlace K)
local notation "P" => ProductSpace (InfinitePlace K)

theorem sourceKPCompactExhaustionTrigMul_chart_eventuallyEq (n : ℕ)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 2 a) (f : T) (b : SourceKPFiniteLevelFiber K hζ)
    (x : P) (hx : x ∈ Ω) :
    sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionTrigMul K hζ n a ha f).val b
      =ᶠ[𝓝 x] fun z => (a ((Real.pi/2)*(1-(sourceKPCompactChartPullback K hζ
        (sourceKPCompactExhaustionC2 K hζ n).val b z).re)) : ℂ) *
          sourceKPCompactChartPullback K hζ f.val b z := by
  filter_upwards [(productUpper_isOpen _).mem_nhds hx] with z hz
  simp only [sourceKPCompactChartPullback,ite_eq_left hz,sourceKPCompactExhaustionTrigMul,
    sourceKPCompactCoreMul,Pi.mul_apply,sourceKPCompactExhaustionAngle,
    sourceKPCompactExhaustionC2_apply,Complex.ofReal_re,mul_comm]

theorem sourceKPCompactExhaustionC2_chart_ofReal_eventuallyEq (n : ℕ)
    (b : SourceKPFiniteLevelFiber K hζ) (x : P) (hx : x ∈ Ω) :
    sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionC2 K hζ n).val b
      =ᶠ[𝓝 x] fun z =>
        ((sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionC2 K hζ n).val b z).re : ℂ) := by
  filter_upwards [(productUpper_isOpen _).mem_nhds hx] with z hz
  simp only [sourceKPCompactChartPullback,ite_eq_left hz,sourceKPCompactExhaustionC2_apply,
    Complex.ofReal_re]

theorem sourceKPCompactExhaustion_trig_energy (n : ℕ) (f : T) (y : Y) :
    sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionCos K hζ n f) y +
      sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionSin K hζ n f) y =
        sourceKPCompactCoreEnergy K hζ f y + (Real.pi/2)^2 * ‖f.val y‖^2 *
          sourceKPCompactCoreEnergy K hζ (sourceKPCompactExhaustionC2 K hζ n) y := by
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ Ω := fun v _ => sourceArchUpperEuclideanMap_positive (p v)
  let E := sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionC2 K hζ n).val b
  let η : P → ℝ := fun z => (E z).re
  let F := sourceKPCompactChartPullback K hζ f.val b
  have hη : DifferentiableAt ℝ η x :=
    Complex.reCLM.differentiableAt.comp x
      (sourceKPCompactChartPullback_differentiableAt K hζ (sourceKPCompactExhaustionC2 K hζ n) b x hx)
  have hF : DifferentiableAt ℝ F x :=
    sourceKPCompactChartPullback_differentiableAt K hζ f b x hx
  have he : E =ᶠ[𝓝 x] fun z => (η z : ℂ) :=
    sourceKPCompactExhaustionC2_chart_ofReal_eventuallyEq K hζ n b x hx
  have ha := sourceKPCompactExhaustionTrigMul_chart_eventuallyEq K hζ n Real.cos Real.contDiff_cos f b x hx
  have hb := sourceKPCompactExhaustionTrigMul_chart_eventuallyEq K hζ n Real.sin Real.contDiff_sin f b x hx
  have hf0 : F x = f.val (sourceKPUpperToCompact K hζ b p) := by
    unfold F sourceKPCompactChartPullback
    rw [ite_eq_left hx]
    change f.val (sourceKPUpperToCompact K hζ b
      (sourceKPArchEuclideanUpperMap K (sourceKPArchUpperEuclideanMap K p))) = _
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
  simp only [sourceKPCompactCoreEnergy_chart,sourceKPCompactCoreEnergyLift,
    sourceKPCompactExhaustionCos,sourceKPCompactExhaustionSin]
  change productGradientEnergy
      (sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionTrigMul K hζ n Real.cos Real.contDiff_cos f).val b) x +
    productGradientEnergy
      (sourceKPCompactChartPullback K hζ (sourceKPCompactExhaustionTrigMul K hζ n Real.sin Real.contDiff_sin f).val b) x =
    productGradientEnergy F x + (Real.pi/2)^2 * ‖f.val (sourceKPUpperToCompact K hζ b p)‖^2 *
      productGradientEnergy E x
  rw [← hf0]
  simp only [productGradientEnergy,productPartial,ha.fderiv_eq (𝕜 := ℝ),
    hb.fderiv_eq (𝕜 := ℝ),he.fderiv_eq (𝕜 := ℝ)]
  exact productGradientEnergy_trig_partition hη hF (Real.pi/2)

end
end ArtinMatthews
