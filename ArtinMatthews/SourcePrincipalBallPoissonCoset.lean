module

public import ArtinMatthews.SourceComplexAdelicCharacter
public import ArtinMatthews.SourceComplexIdealBasis
public import ArtinMatthews.SourceComplexTensorRapid
public import ArtinMatthews.SourcePrincipalBallCoset
public import ArtinMatthews.SourceComplexIdealSummability
public import ArtinMatthews.SourceFractionalIdealDualValuation
public import ArtinMatthews.SourceNumberFieldIdealPoisson
public import ArtinMatthews.SourcePrincipalBallQuotientKernel
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Shifted lattice Poisson on each exterior coset. Its positive trace
phase is the actual source S-character on the chosen coset lift. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization StandardAdelic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical nonZeroDivisors SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

theorem sourceComplexPoisson_field_phase (a b : K) :
    archCharacter K
      (sourceComplexPlaceAdele K (sourceComplexFieldEmbedding K a) *
        sourceComplexPlaceAdele K (sourceComplexFieldEmbedding K b)) =
      rationalCharacter K (a * b) := by
  rw [sourceComplexTraceForm_positive_character, sourceComplexTraceForm_field,
    RealCharacters.LocalAnalysis.realCharacter_apply, mul_one]
  change _ = archCharacter K (algebraMap K (InfiniteAdeleRing K) (a * b))
  rw [archCharacter_rational]
  push_cast
  congr 1
  ring

omit [IsTotallyComplex K] in
theorem sourceSCharacter_norm (x : K) : ‖sCharacter K S x‖ = 1 := by
  change ‖rationalCharacter K x * ∏ P ∈ S,
    localFiniteCharacter K P (algebraMap K (P.adicCompletion K) x)‖ = 1
  rw [norm_mul, rationalCharacter_unitary, one_mul, norm_prod]
  exact Finset.prod_eq_one (fun P _ => localFiniteCharacter_unitary K P _)

theorem sourcePrincipalBallPoissonCoset_phase (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (q : sourcePrincipalBallModulusQuotient K S₀ M)
    (y : (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val) :
    archCharacter K
      (sourceComplexPlaceAdele K (sourceComplexFieldEmbedding K (y : K)) *
        sourceComplexPlaceAdele K
          (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K))) =
      sCharacter K S ((y : K) * (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K)) := by
  rw [sourceComplexPoisson_field_phase]
  exact (sourceFiniteBallIdeal_product_dual_phase K S e (M : FI)
    (FractionalIdeal.coeIdeal_ne_zero.mpr hM)
    (sourcePrincipalExteriorModulus_count_inS K S₀ M hM hc) _ _
    (sourcePrincipalBallCosetRepresentative K S₀ e M hc q).property y.property).symm

theorem sourcePrincipalBallPoissonCoset (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (f : CPlaces → 𝓢(ℂ, ℂ))
    (q : sourcePrincipalBallModulusQuotient K S₀ M) :
    (((FractionalIdeal.absNorm (sourcePrincipalBallProductUnit K S₀ e M hM).val : ℝ) *
      Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) *
      (∑' y : (sourcePrincipalBallProductUnit K S₀ e M hM).val.val,
        sourceComplexTensor f
          (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K) +
            sourceComplexFieldEmbedding K (y : K))) =
      ∑' y : (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val,
        sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (y : K)) *
          sCharacter K S ((y : K) * (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K)) := by
  refine (sourceNumberFieldIdealPoisson K (sourcePrincipalBallProductUnit K S₀ e M hM) f
    (sourceComplexFieldEmbedding K (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K))).symm.trans ?_
  exact tsum_congr (fun y => by rw [sourcePrincipalBallPoissonCoset_phase K S₀ e M hM hc q y])

theorem sourcePrincipalBallDualFourier_summable_norm (I : FIˣ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    Summable (fun y : (mixedTraceDualIdeal K I).val =>
      ‖sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (y : K))‖) := by
  simpa only [sourceNumberFieldComplexFourier_eq, norm_mul, sourceRealCharacter_norm, mul_one] using
    sourceComplexDualIdealFourier_summable_norm K I f 0

end
end ArtinMatthews.SourcePhysical
