module

public import ArtinMatthews.SourceKPArchJacquetProfile
public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceArchWeightedDiagonalScale
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

/-! The full archimedean product uses the actual embedded frequency and
the same rationally dilated height as the adelic change of variables. -/

namespace ArtinMatthews
open NumberField SourceArchJacquet StandardAdelic
open scoped NumberField AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPTraceJacquetArchProfile_frequency_scale (m : Kˣ) (s : ℂ)
    (y : InfinitePlace K → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPTraceJacquetArchProfile K hζ m s y =
      (∏ v : InfinitePlace K,
        (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ) ^ (2 * s - 1)) *
        sourceKPTraceJacquetArchProfile K hζ 1 s (sourceKPCuspRationalHeight K hζ m y) := by
  classical
  unfold sourceKPTraceJacquetArchProfile sourceArchWeightedProduct
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  let b := sourceKPCuspRationalComplexUnit K hζ m v
  let u : ℂˣ := Units.mk0 (y v : ℂ) (Complex.ofReal_ne_zero.mpr (hy v).ne')
  have hu : ‖(u : ℂ)‖ = y v := by
    change ‖(y v : ℂ)‖ = y v
    rw [Complex.norm_real, Real.norm_of_nonneg (hy v).le]
  have hm : sourceKPTraceJacquetProfileFrequency K hζ m v = -(b : ℂ) := rfl
  have hone : sourceKPTraceJacquetProfileFrequency K hζ 1 v = -1 := by
    change -(sourceKPArchComplexEquiv K hζ v (algebraMap K v.Completion (1 : K))) = -1
    rw [map_one (algebraMap K v.Completion), map_one (sourceKPArchComplexEquiv K hζ v)]
  have h := sourceArchWeightedDiagonalProfile_frequency_scale sourceArchTraceCharacter s b u
  rw [Units.val_mul, norm_mul, hu] at h
  rw [hm, hone]
  exact h

end
end ArtinMatthews
