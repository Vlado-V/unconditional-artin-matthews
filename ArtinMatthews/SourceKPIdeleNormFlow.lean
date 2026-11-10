module

public import ArtinMatthews.SourceArchOnlyIdele
public import ArtinMatthews.SourceArchIwasawaCompletion
public import ArtinMatthews.SourceKPAdelicCompactIntersection
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

/-! A continuous positive norm section supported at one actual complex
place. Its finite coordinates are identically one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPIdeleNormFlowArch (v₀ : InfinitePlace K) (t : ℝ) : (InfiniteAdeleRing K)ˣ where
  val v := (sourceKPArchComplexEquiv K hζ v).symm
    (Complex.exp (if v = v₀ then (t : ℂ)/2 else 0))
  inv v := (sourceKPArchComplexEquiv K hζ v).symm
    (Complex.exp (-(if v = v₀ then (t : ℂ)/2 else 0)))
  val_inv := by
    funext v
    change (sourceKPArchComplexEquiv K hζ v).symm _ *
      (sourceKPArchComplexEquiv K hζ v).symm _ = 1
    rw [← map_mul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, map_one]
  inv_val := by
    funext v
    change (sourceKPArchComplexEquiv K hζ v).symm _ *
      (sourceKPArchComplexEquiv K hζ v).symm _ = 1
    rw [← map_mul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, map_one]

def sourceKPIdeleNormFlow (v₀ : InfinitePlace K) (t : ℝ) : IdeleGroup (𝓞 K) K :=
  sourceArchOnlyIdele K (sourceKPIdeleNormFlowArch K hζ v₀ t)

theorem sourceKPIdeleNormFlowArch_coordinate (v₀ v : InfinitePlace K) (t : ℝ) :
    ‖(sourceKPIdeleNormFlowArch K hζ v₀ t : InfiniteAdeleRing K) v‖ =
      if v = v₀ then Real.exp (t/2) else 1 := by
  classical
  rw [← sourceKPArchComplexEquiv_norm K hζ v]
  change ‖(sourceKPArchComplexEquiv K hζ v)
    ((sourceKPArchComplexEquiv K hζ v).symm _)‖ = _
  rw [RingEquiv.apply_symm_apply]
  by_cases hv : v = v₀
  · norm_num [hv, Complex.norm_exp]
  · simp only [hv, ite_false, Complex.exp_zero, norm_one]

theorem sourceKPIdeleNormFlow_norm (v₀ : InfinitePlace K) (t : ℝ) :
    sourceKPIdeleAbsoluteNorm K (sourceKPIdeleNormFlow K hζ v₀ t) = Real.exp t := by
  classical
  have := source_isTotallyComplex K hζ
  rw [sourceKPIdeleNormFlow, sourceArchOnlyIdele_norm, InfiniteAdeleRing.norm_def,
    Finset.prod_eq_single v₀]
  · rw [sourceKPIdeleNormFlowArch_coordinate, ite_eq_left rfl, NumberField.IsTotallyComplex.mult_eq]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  · intro v _ hv
    rw [sourceKPIdeleNormFlowArch_coordinate, ite_eq_right hv, one_pow]
  · exact fun h => (h (Finset.mem_univ v₀)).elim

theorem sourceKPIdeleNormFlow_finite (v₀ : InfinitePlace K) (t : ℝ) :
    sourceKPIdeleFiniteUnit K (sourceKPIdeleNormFlow K hζ v₀ t) = 1 :=
  sourceArchOnlyIdele_finite K _

theorem sourceKPIdeleNormFlowArch_zero (v₀ : InfinitePlace K) :
    sourceKPIdeleNormFlowArch K hζ v₀ 0 = 1 := by
  classical
  apply Units.ext
  funext v
  change (sourceKPArchComplexEquiv K hζ v).symm
    (Complex.exp (if v = v₀ then (0 : ℂ)/2 else 0)) = 1
  simp

theorem sourceKPIdeleNormFlow_zero (v₀ : InfinitePlace K) :
    sourceKPIdeleNormFlow K hζ v₀ 0 = 1 := by
  rw [sourceKPIdeleNormFlow, sourceKPIdeleNormFlowArch_zero, map_one]

theorem sourceKPIdeleNormFlow_add (v₀ : InfinitePlace K) (s t : ℝ) :
    sourceKPIdeleNormFlow K hζ v₀ (s+t) =
      sourceKPIdeleNormFlow K hζ v₀ s * sourceKPIdeleNormFlow K hζ v₀ t := by
  unfold sourceKPIdeleNormFlow
  rw [← map_mul]
  congr 1
  apply Units.ext
  funext v
  change (sourceKPArchComplexEquiv K hζ v).symm _ =
    (sourceKPArchComplexEquiv K hζ v).symm _ * (sourceKPArchComplexEquiv K hζ v).symm _
  rw [← map_mul, ← Complex.exp_add]
  congr 2
  split_ifs <;> push_cast <;> ring

private theorem sourceKPNormFlow_complexSymm_continuous (v : InfinitePlace K) :
    Continuous (sourceKPArchComplexEquiv K hζ v).symm := by
  apply Isometry.continuous
  apply isometry_iff_dist_eq.mpr
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub,
    ← sourceKPArchComplexEquiv_norm K hζ v, RingEquiv.apply_symm_apply]

theorem sourceKPIdeleNormFlowArch_continuous (v₀ : InfinitePlace K) :
    Continuous (sourceKPIdeleNormFlowArch K hζ v₀) := by
  classical
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_pi
    intro v
    change Continuous (fun t : ℝ => (sourceKPArchComplexEquiv K hζ v).symm
      (Complex.exp (if v = v₀ then (t : ℂ)/2 else 0)))
    apply (sourceKPNormFlow_complexSymm_continuous K hζ v).comp
    by_cases hv : v = v₀
    · simp only [hv, ite_true]
      exact Complex.continuous_exp.comp (Complex.continuous_ofReal.div_const 2)
    · simp only [hv, ite_false]
      exact continuous_const
  · apply continuous_pi
    intro v
    change Continuous (fun t : ℝ => (sourceKPArchComplexEquiv K hζ v).symm
      (Complex.exp (-(if v = v₀ then (t : ℂ)/2 else 0))))
    apply (sourceKPNormFlow_complexSymm_continuous K hζ v).comp
    by_cases hv : v = v₀
    · simp only [hv, ite_true]
      exact Complex.continuous_exp.comp (Complex.continuous_ofReal.div_const 2).neg
    · simp only [hv, ite_false]
      exact continuous_const

theorem sourceKPIdeleNormFlow_continuous (v₀ : InfinitePlace K) :
    Continuous (sourceKPIdeleNormFlow K hζ v₀) := by
  apply Units.continuous_iff.mpr
  constructor
  · exact ((Units.continuous_val.comp
      (sourceKPIdeleNormFlowArch_continuous K hζ v₀)).prodMk continuous_const)
  · exact ((Units.continuous_val.comp
      (sourceKPIdeleNormFlowArch_continuous K hζ v₀).inv).prodMk continuous_const)

end
end ArtinMatthews
