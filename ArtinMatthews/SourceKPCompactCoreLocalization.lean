module

public import ArtinMatthews.SourceKPFiniteChartCoordinates
public import ArtinMatthews.SourceHyperbolicH1LocalTests
public import ArtinMatthews.SourceKPCompactC2Core
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

namespace ArtinMatthews
open NumberField MeasureTheory Filter SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

/-- Multiplication by a local compact test extends a locally smooth function to a global test. -/
def h1LocalTestMul {ι : Type*} [Fintype ι]
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (η : h1LocalTests U) (F : ProductSpace ι → ℂ) (hF : ContDiffOn ℝ 2 F U) :
    h1LocalTests U := by
  let g : ProductSpace ι → ℂ := fun x => η.val.val x * F x
  have hs : tsupport g ⊆ tsupport η.val.val := tsupport_mul_subset_left
  have hc : ContDiff ℝ 2 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact η.val.prop.1.contDiffAt.mul ((hF x hx).contDiffAt (hU.mem_nhds hx))
    · have hη : η.val.val =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (η.prop h))
      have hg : g =ᶠ[𝓝 x] 0 := by
        filter_upwards [hη] with y hy
        simp only [g, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hg
  refine ⟨⟨g, hc, ?_, hs.trans (η.prop.trans hUupper)⟩, hs.trans η.prop⟩
  exact η.val.prop.2.1.mul_right

theorem h1LocalTestMul_apply {ι : Type*} [Fintype ι]
    (U : Set (ProductSpace ι)) (hU : IsOpen U) (hUupper : U ⊆ productUpper ι)
    (η : h1LocalTests U) (F : ProductSpace ι → ℂ) (hF : ContDiffOn ℝ 2 F U)
    (x : ProductSpace ι) :
    (h1LocalTestMul U hU hUupper η F hF).val.val x = η.val.val x * F x := rfl

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCompactCoreLocalized (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p)) :
    h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p) :=
  h1LocalTestMul _ (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p) η
    (sourceKPCompactChartPullback K hζ f.val b)
    ((f.prop.2.2 b).mono (sourceKPFiniteChartCoordinateDomain_upper K hζ b p))

theorem sourceKPCompactCoreLocalized_apply (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p))
    (x : ProductSpace (InfinitePlace K)) :
    (sourceKPCompactCoreLocalized K hζ f b p η).val.val x =
      η.val.val x * sourceKPCompactChartPullback K hζ f.val b x := rfl

theorem sourceKPCompactCoreLocalized_gradient_eq (f : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
    (η : h1LocalTests (sourceKPFiniteChartCoordinateDomain K hζ b p))
    (x : ProductSpace (InfinitePlace K)) (hη : η.val.val =ᶠ[𝓝 x] 1) :
    productGradientEnergy (sourceKPCompactCoreLocalized K hζ f b p η).val.val x =
      sourceKPCompactCoreEnergyLift K hζ f b x := by
  have he : (sourceKPCompactCoreLocalized K hζ f b p η).val.val =ᶠ[𝓝 x]
      sourceKPCompactChartPullback K hζ f.val b := by
    filter_upwards [hη] with y hy
    rw [sourceKPCompactCoreLocalized_apply, hy]
    simp
  change productGradientEnergy (sourceKPCompactCoreLocalized K hζ f b p η).val.val x =
    productGradientEnergy (sourceKPCompactChartPullback K hζ f.val b) x
  simp only [productGradientEnergy, productPartial, he.fderiv_eq (𝕜 := ℝ)]

end
end ArtinMatthews
