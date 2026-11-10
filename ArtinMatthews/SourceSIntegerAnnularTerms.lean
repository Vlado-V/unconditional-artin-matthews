module

public import ArtinMatthews.SourcePrincipalBallDualSupport
public import ArtinMatthews.SourceFiniteDilationDual
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

/-! The exact primal and dual annular summands as finite sums of the
genuine ball-lattice summands, including all signs and local volumes. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization
open scoped NumberField Classical nonZeroDivisors BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourceFiniteFieldEmbedding (T : Finset (HeightOneSpectrum (𝓞 K))) (x : K) : SFiniteSpace K T :=
  fun v => algebraMap K (v.val.adicCompletion K) x

def sourceSIntegerAnnularPrimalTerm (a : OS) (w : OS ⧸ Ideal.span {a} → ℂ)
    (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) (x : OS) : ℂ :=
  w (Ideal.Quotient.mk _ x) * sourceComplexTensor f (sourceComplexFieldEmbedding K (x : K)) *
    sourceFiniteUnitTest K S (sourceFiniteDilationPoint K S t (x : K))

def sourceSIntegerAnnularDualTerm (a : OS) (ha : a ≠ 0) (w : OS ⧸ Ideal.span {a} → ℂ)
    (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) (h : OS) : ℂ :=
  sourceNumberFieldComplexFourier K (sourceComplexTensor f)
      (sourceComplexFieldEmbedding K ((h : K) / (a : K))) *
    sourcePrincipalQuotientFourier K S₀ a ha w h *
    sourceFiniteLocalFourier K S (sourceFiniteUnitTest K S)
      (sourceFiniteDilationMul K S t (sourceFiniteFieldEmbedding K S ((h : K) / (a : K))))

theorem sourceSIntegerAnnularPrimalTerm_patterns (a : OS) (w : OS ⧸ Ideal.span {a} → ℂ)
    (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) (x : OS) :
    sourceSIntegerAnnularPrimalTerm K S₀ a w f t x =
      ∑ b : S → Fin 2, (∏ v : S, sourceFiniteChoiceSign (b v)) *
        sourcePrincipalBallPrimalTerm K S₀ (sourceFiniteDilationExponent K S t b) a w f x := by
  unfold sourceSIntegerAnnularPrimalTerm
  rw [sourceFiniteUnitTest_dilation_ideal_expansion K S t x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold sourcePrincipalBallPrimalTerm
  by_cases hx : (x : K) ∈ sourceFiniteDilationIdeal K S t b
  · rw [ite_eq_left hx, Set.indicator_of_mem (show x ∈ sourcePrincipalBallIntegerSet K S₀
      (sourceFiniteDilationExponent K S t b) from hx)]
    ring
  · rw [ite_eq_right hx, Set.indicator_of_notMem (show x ∉ sourcePrincipalBallIntegerSet K S₀
      (sourceFiniteDilationExponent K S t b) from hx), mul_zero, mul_zero]

theorem sourceSIntegerAnnularDualTerm_patterns (a : OS) (ha : a ≠ 0)
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) (h : OS) :
    (sourceFiniteDilationNorm K S t : ℂ) * sourceSIntegerAnnularDualTerm K S₀ a ha w f t h =
      ∑ b : S → Fin 2, ((∏ v : S, sourceFiniteChoiceSign (b v)) *
          (sourceFiniteBallVolume K S₀ (sourceFiniteDilationExponent K S t b) : ℂ)) *
        sourcePrincipalBallDualTerm K S₀ (sourceFiniteDilationExponent K S t b) a ha w f h := by
  let y := sourceFiniteFieldEmbedding K S ((h : K) / (a : K))
  let D := sourceNumberFieldComplexFourier K (sourceComplexTensor f)
      (sourceComplexFieldEmbedding K ((h : K) / (a : K))) *
    sourcePrincipalQuotientFourier K S₀ a ha w h
  change (sourceFiniteDilationNorm K S t : ℂ) *
    (D * sourceFiniteLocalFourier K S (sourceFiniteUnitTest K S) (sourceFiniteDilationMul K S t y)) = _
  rw [mul_left_comm, ← sourceFiniteDilationDualWeight_sum K S t y, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold sourceFiniteDilationDualWeight sourcePrincipalBallDualTerm
  by_cases hx : h ∈ sourcePrincipalBallFrequencySet K S₀ (sourceFiniteDilationExponent K S t b) a
  · have hy : ∀ v : S, y v ∈ sourceLocalBall K v.val
        ((sourceDifferentExponent K v.val : ℤ) + sourceFiniteDilationExponent K S t b v) := hx
    rw [ite_eq_left hy, Set.indicator_of_mem hx]
    change D * ((∏ v : S, sourceFiniteChoiceSign (b v)) *
        (sourceFiniteBallVolume K S₀ (sourceFiniteDilationExponent K S t b) : ℂ)) = _ * D
    exact mul_comm _ _
  · have hy : ¬ ∀ v : S, y v ∈ sourceLocalBall K v.val
        ((sourceDifferentExponent K v.val : ℤ) + sourceFiniteDilationExponent K S t b v) := hx
    rw [ite_eq_right hy, Set.indicator_of_notMem hx, mul_zero, mul_zero]

end
end ArtinMatthews.SourcePhysical
