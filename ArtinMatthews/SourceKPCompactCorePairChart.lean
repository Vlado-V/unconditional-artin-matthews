module

public import ArtinMatthews.SourceKPCompactDirichletCore
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

/-! The descended pairing in each actual finite-cover chart. -/
namespace ArtinMatthews
open NumberField SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace BigOperators ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactCorePairDensity_chart (f g : sourceKPCompactC2Core K hζ)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    sourceKPCompactCorePairDensity K hζ f g (sourceKPUpperToCompact K hζ b p) =
      productGradientPair (sourceKPCompactChartPullback K hζ f.val b)
        (sourceKPCompactChartPullback K hζ g.val b) (sourceKPArchUpperEuclideanMap K p) := by
  let x := sourceKPArchUpperEuclideanMap K p
  have hx : x ∈ productUpper (InfinitePlace K) :=
    fun i _ => sourceArchUpperEuclideanMap_positive (p i)
  let D := sourceKPCompactCoreGradientLiftLinear K hζ b x hx
  have hn (u : sourceKPCompactC2Core K hζ) :
      ‖D u‖ ^ 2 = sourceKPCompactCoreEnergy K hζ u (sourceKPUpperToCompact K hζ b p) := by
    rw [sourceKPCompactCoreEnergy_chart]
    exact sourceKPCompactCoreGradientLift_norm_sq K hζ u b x
  have hp := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (D f) (D g)
  change inner ℂ (D f) (D g) = ((‖D f+D g‖ : ℂ)^2 - (‖D f-D g‖ : ℂ)^2 +
    ((‖D f-Complex.I • D g‖ : ℂ)^2 - (‖D f+Complex.I • D g‖ : ℂ)^2)*Complex.I)/4 at hp
  rw [sourceKPCompactCorePairDensity_polarization]
  have he := by
    simpa only [← D.map_smul Complex.I g,← D.map_add f g,← D.map_sub f g,
      ← D.map_add f (Complex.I • g),← D.map_sub f (Complex.I • g),← Complex.ofReal_pow,hn] using hp
  rw [← he]
  change inner ℂ (sourceKPCompactCoreGradientLift K hζ f b x)
    (sourceKPCompactCoreGradientLift K hζ g b x) = _
  rw [PiLp.inner_apply, Fintype.sum_prod_type]
  simp only [sourceKPCompactCoreGradientLift,WithLp.ofLp_toLp,RCLike.inner_apply,
    productGradientPair,map_mul,Finset.mul_sum,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [x]
  rw [Complex.star_def,Complex.conj_ofReal]
  ring

end
end ArtinMatthews
