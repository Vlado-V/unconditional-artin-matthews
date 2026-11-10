module

public import ArtinMatthews.SourceKPTranslateCoreGradientPair
public import ArtinMatthews.SourceKPTranslateCoreGram
public import ArtinMatthews.SourceKPCompactDirichletCore
public import ArtinMatthews.SourceKPCompactCorePairChart
public import ArtinMatthews.SourceKPProductGradientPairTransport
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

/-! The gradient of the actual finite trace is the sum of native
gradients. Both pairings descend as literal traces of the cross density. -/
namespace ArtinMatthews
open NumberField Matrix SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace ContDiff BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "F" => SourceKPFiniteLevelFiber K hζ
local notation "FJ" => SourceKPTranslateFiniteLevelFiber K hζ T
local notation "U" => SourceKPArchUpperHalfSpace K
local notation "P" => ProductSpace (InfinitePlace K)
local notation "C2" => sourceKPCompactC2Core K hζ
local notation "φ[" t ", " ht "]" => sourceKPFiniteRightTranslateMap K hζ T t ht
local notation "L[" t ", " ht ", " b "]" => {c : FJ // φ[t, ht] c = b}

theorem sourceKPTranslateCoreGram_gradientLift (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f : C2) (b : F) (x : P) (hx : x ∈ productUpper (InfinitePlace K)) :
    sourceKPCompactCoreGradientLift K hζ (sourceKPTranslateCoreGram K hζ T t ht u hu f) b x =
      ∑ c : L[t, ht, b], sourceKPCompactCoreGradientLift K hζ f (φ[u, hu] c.val) x := by
  let A (c : L[t, ht, b]) := sourceKPCompactChartPullback K hζ f.val (φ[u, hu] c.val)
  have hd : fderiv ℝ (fun y => ∑ c : L[t, ht, b], A c y) x =
      ∑ c : L[t, ht, b], fderiv ℝ (A c) x :=
    fderiv_fun_sum (fun c _ => sourceKPCompactChartPullback_differentiableAt K hζ f (φ[u, hu] c.val) x hx)
  rw [sourceKPCompactCoreGradientLift_differential,sourceKPTranslateCoreGram_chart]
  change sourceProductGradientOfDifferential x (fderiv ℝ (fun y => ∑ c : L[t, ht, b], A c y) x) = _
  rw [hd,map_sum]
  apply Finset.sum_congr rfl
  intro c _
  exact (sourceKPCompactCoreGradientLift_differential K hζ f (φ[u, hu] c.val) x).symm

theorem sourceKPCompactCorePairDensity_gradientLift_chart (f g : C2) (b : F) (p : U) :
    sourceKPCompactCorePairDensity K hζ f g (sourceKPUpperToCompact K hζ b p) =
      inner ℂ (sourceKPCompactCoreGradientLift K hζ f b (sourceKPArchUpperEuclideanMap K p))
        (sourceKPCompactCoreGradientLift K hζ g b (sourceKPArchUpperEuclideanMap K p)) := by
  rw [sourceKPCompactCorePairDensity_chart]
  simp only [sourceKPCompactCoreGradientLift_differential,sourceProductGradientOfDifferential_inner]

theorem sourceKPCompactCorePairDensity_gram_right_eq_trace (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) :
    sourceKPCompactCorePairDensity K hζ f (sourceKPTranslateCoreGram K hζ T t ht u hu g) =
      sourceKPTranslateCompactTrace K hζ T t ht (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g) := by
  funext y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ productUpper (InfinitePlace K) := fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  rw [sourceKPCompactCorePairDensity_gradientLift_chart]
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ f b x)
    (sourceKPCompactCoreGradientLift K hζ (sourceKPTranslateCoreGram K hζ T t ht u hu g) b x) = _
  rw [sourceKPTranslateCoreGram_gradientLift K hζ T t ht u hu g b x hx,inner_sum,
    sourceKPTranslateCompactTrace_upper]
  apply Finset.sum_congr rfl
  intro c _
  rw [sourceKPTranslateCoreGradientPair_upper]
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ f b x)
    (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] c.val) x) =
      inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] c.val) x)
        (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] c.val) x)
  rw [c.prop]

theorem sourceKPCompactCorePairDensity_gram_left_eq_trace (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u)
    (f g : C2) :
    sourceKPCompactCorePairDensity K hζ (sourceKPTranslateCoreGram K hζ T u hu t ht f) g =
      sourceKPTranslateCompactTrace K hζ T u hu (sourceKPTranslateCoreGradientPair K hζ T t ht u hu f g) := by
  funext y
  obtain ⟨b,p,rfl⟩ := sourceKPUpperToCompact_cover K hζ y
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ productUpper (InfinitePlace K) := fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  rw [sourceKPCompactCorePairDensity_gradientLift_chart]
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ (sourceKPTranslateCoreGram K hζ T u hu t ht f) b x)
    (sourceKPCompactCoreGradientLift K hζ g b x) = _
  rw [sourceKPTranslateCoreGram_gradientLift K hζ T u hu t ht f b x hx,sum_inner,
    sourceKPTranslateCompactTrace_upper]
  apply Finset.sum_congr rfl
  intro c _
  rw [sourceKPTranslateCoreGradientPair_upper]
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] c.val) x)
    (sourceKPCompactCoreGradientLift K hζ g b x) =
      inner ℂ (sourceKPCompactCoreGradientLift K hζ f (φ[t, ht] c.val) x)
        (sourceKPCompactCoreGradientLift K hζ g (φ[u, hu] c.val) x)
  rw [c.prop]

end
end ArtinMatthews
