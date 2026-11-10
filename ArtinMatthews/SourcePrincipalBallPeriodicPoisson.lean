module

public import ArtinMatthews.SourceComplexAdelicCharacter
public import ArtinMatthews.SourcePrincipalBallPeriodicSum
public import ArtinMatthews.SourcePrincipalBallPoissonCoset
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

/-! The weighted periodic Poisson identity for a single actual ball
ideal. The finite dual weight is the full source quotient transform. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization StandardAdelic
open scoped NumberField Classical nonZeroDivisors BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "S" => principalizingSet S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourcePrincipalBallCovolume (e : S → ℤ) (M : Ideal (𝓞 K)) (hM : M ≠ ⊥) : ℝ :=
  (FractionalIdeal.absNorm (sourcePrincipalBallProductUnit K S₀ e M hM).val : ℝ) * Real.sqrt |(discr K : ℝ)|

def sourcePrincipalBallDualCoefficient (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (y : K) : ℂ :=
  ∑' q : sourcePrincipalBallModulusQuotient K S₀ M, w q *
    sCharacter K S (y * (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K))

theorem sourcePrincipalBallDualCoefficient_norm_le (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (y : K) :
    ‖sourcePrincipalBallDualCoefficient K S₀ e M hc w y‖ ≤
      ∑' q : sourcePrincipalBallModulusQuotient K S₀ M, ‖w q‖ := by
  let : Finite (sourcePrincipalBallModulusQuotient K S₀ M) :=
    sourcePrincipalBallModulusQuotient_finite K S₀ M hM hc
  let : Fintype (sourcePrincipalBallModulusQuotient K S₀ M) := Fintype.ofFinite _
  unfold sourcePrincipalBallDualCoefficient
  simp only [tsum_fintype]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun q _ => by
    rw [norm_mul, sourceSCharacter_norm, mul_one]))

variable [IsTotallyComplex K]

theorem sourcePrincipalBallDualWeighted_summable_norm (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    Summable (fun y : (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val =>
      ‖sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (y : K)) *
        sourcePrincipalBallDualCoefficient K S₀ e M hc w (y : K)‖) := by
  have h := Summable.mul_right (∑' q : sourcePrincipalBallModulusQuotient K S₀ M, ‖w q‖)
    (sourcePrincipalBallDualFourier_summable_norm K (sourcePrincipalBallProductUnit K S₀ e M hM) f)
  refine h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (sourcePrincipalBallDualCoefficient_norm_le K S₀ e M hM hc w (y : K))
    (norm_nonneg _)

theorem sourcePrincipalBallPeriodicPoisson (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (w : sourcePrincipalBallModulusQuotient K S₀ M → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (sourcePrincipalBallCovolume K S₀ e M hM : ℂ) *
      (∑' x : (sourceFiniteBallIdeal K S e).val, sourcePrincipalBallWeightedTerm K S₀ e M w f x) =
      ∑' y : (mixedTraceDualIdeal K (sourcePrincipalBallProductUnit K S₀ e M hM)).val,
        sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (y : K)) *
          sourcePrincipalBallDualCoefficient K S₀ e M hc w (y : K) := by
  let Q := sourcePrincipalBallModulusQuotient K S₀ M
  let : Finite Q := sourcePrincipalBallModulusQuotient_finite K S₀ M hM hc
  let : Fintype Q := Fintype.ofFinite Q
  let I := sourcePrincipalBallProductUnit K S₀ e M hM
  let g (q : Q) (y : (mixedTraceDualIdeal K I).val) :=
    w q * (sourceNumberFieldComplexFourier K (sourceComplexTensor f) (sourceComplexFieldEmbedding K (y : K)) *
      sCharacter K S ((y : K) * (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K)))
  have hg (q : Q) : Summable (fun y => g q y) := by
    apply Summable.of_norm
    simp_rw [g, norm_mul, sourceSCharacter_norm, mul_one]
    exact (sourcePrincipalBallDualFourier_summable_norm K I f).mul_left _
  rw [sourcePrincipalBallWeightedSum_reindex K S₀ e M hM hc]
  calc
    _ = ∑ q : Q, ∑' y, g q y := by
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_left_comm, sourcePrincipalBallCovolume, sourcePrincipalBallPoissonCoset K S₀ e M hM hc f q]
      exact (tsum_mul_left).symm
    _ = ∑' y, ∑ q : Q, g q y := (Summable.tsum_finsetSum (fun q _ => hg q)).symm
    _ = _ := by
      apply tsum_congr
      intro y
      unfold sourcePrincipalBallDualCoefficient
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      unfold g
      ring

end
end ArtinMatthews.SourcePhysical
