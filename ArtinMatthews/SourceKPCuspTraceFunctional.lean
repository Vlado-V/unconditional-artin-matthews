module

public import ArtinMatthews.SourceKPCuspTraceFrequency
public import ArtinMatthews.SourceKPMinkowskiCuspLattice
public import ArtinMatthews.VaryingKummerAnalyticMixedTraceDual
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

/-! The actual trace frequency as a real functional on the scaled Minkowski coordinates. -/
namespace ArtinMatthews
open NumberField Module Module.Free
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "E" => mixedEmbedding.mixedSpace K

def sourceKPCuspTraceFunctional (ξ : K) : E →L[ℝ] ℝ :=
  (innerSL ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ))).comp
    (mixedEmbedding.euclidean.toMixed K).symm.toContinuousLinearMap

theorem sourceKPCuspTraceFunctional_embedding (ξ a : K) :
    sourceKPCuspTraceFunctional K ξ (mixedEmbedding K a) = (Algebra.trace ℚ K (a * ξ) : ℝ) := by
  change inner ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ)) (mixedFieldEmbedding K a) = _
  rw [real_inner_comm]
  exact mixedTraceTransform_inner_eq_trace K a ξ

variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

theorem sourceKPCuspTraceFunctional_basis (n : I → ℤ) (i : I) :
    sourceKPCuspTraceFunctional K (sourceKPCuspTraceFrequency K d n)
      (sourceKPCuspLatticeBasis K d hd i) = (n i : ℝ) := by
  rw [sourceKPCuspLatticeBasis_apply, sourceKPCuspTraceFunctional_embedding, mul_comm]
  exact sourceKPCuspTraceFrequency_pair K d hd n i

theorem sourceKPCuspTraceFunctional_coordinates (n : I → ℤ) (x : E) :
    sourceKPCuspTraceFunctional K (sourceKPCuspTraceFrequency K d n) x =
      ∑ i, sourceKPCuspCoordinates K d hd x i * (n i : ℝ) := by
  conv_lhs => rw [← (sourceKPCuspLatticeBasis K d hd).sum_repr x]
  simp only [map_sum, map_smul, sourceKPCuspTraceFunctional_basis, smul_eq_mul]
  rfl

omit hd in
 theorem sourceKPCuspTraceFunctional_stdBasis (ξ : K) (a : mixedEmbedding.index K) :
    sourceKPCuspTraceFunctional K ξ (mixedEmbedding.stdBasis K a) =
      (mixedEmbedding.stdBasis K).repr
        (mixedTraceTransformRaw K (mixedEmbedding K ξ)) a := by
  have he : (mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding.stdBasis K a) =
      mixedEmbedding.euclidean.stdOrthonormalBasis K a := by
    apply (mixedEmbedding.euclidean.toMixed K).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    have h := congrArg (fun b : Basis (mixedEmbedding.index K) ℝ E => b a)
      (mixedEmbedding.euclidean.stdOrthonormalBasis_map_eq (K := K))
    exact h.symm
  change inner ℝ (mixedTraceTransform K (mixedFieldEmbedding K ξ))
    ((mixedEmbedding.euclidean.toMixed K).symm (mixedEmbedding.stdBasis K a)) = _
  rw [he, real_inner_comm, ← OrthonormalBasis.repr_apply_apply]
  rfl

variable [IsTotallyComplex K]

def sourceKPCuspHorizontalDirection (v : InfinitePlace K) (k : Fin 2) : E :=
  mixedEmbedding.stdBasis K (Sum.inr (⟨v, IsTotallyComplex.isComplex v⟩, k))

omit hd in
 theorem sourceKPCuspTraceFunctional_horizontal_zero (ξ : K) (v : InfinitePlace K) :
    sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v 0) =
      2 * (v.embedding ξ).re := by
  rw [sourceKPCuspHorizontalDirection, sourceKPCuspTraceFunctional_stdBasis,
    mixedEmbedding.stdBasis_apply_isComplex_fst]
  simp [mixedTraceTransformRaw]

omit hd in
 theorem sourceKPCuspTraceFunctional_horizontal_one (ξ : K) (v : InfinitePlace K) :
    sourceKPCuspTraceFunctional K ξ (sourceKPCuspHorizontalDirection K v 1) =
      -(2 * (v.embedding ξ).im) := by
  rw [sourceKPCuspHorizontalDirection, sourceKPCuspTraceFunctional_stdBasis,
    mixedEmbedding.stdBasis_apply_isComplex_snd]
  simp [mixedTraceTransformRaw]

end
end ArtinMatthews
