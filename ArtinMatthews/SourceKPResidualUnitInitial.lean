module

public import ArtinMatthews.SourceKPArchJacquetProfile
public import ArtinMatthews.SourceKPCuspRationalHeight
public import ArtinMatthews.SourceKPArchJacquetFrequencyPositivity
public import ArtinMatthews.SourceKPArchJacquetFrequencyScale
public import ArtinMatthews.SourceKPCuspHeightJacquetProfile
public import ArtinMatthews.SourceKPTraceJacquetPositiveHeight
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

namespace ArtinMatthews
open NumberField MeasureTheory StandardAdelic
open scoped NumberField AdeleRing MatrixGroups BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ

def sourceKPCuspResidualUnitTranslate (m : Kˣ) (qf : Gf) : Gf :=
  (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2*qf

def sourceKPCuspResidualFrequencyScale (m : Kˣ) (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace K,
    (‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ : ℂ)^(2*s-1)

def sourceKPCuspResidualUnitArchValue (s : ℂ) : ℂ :=
  sourceKPTraceJacquetArchProfile K hζ (1 : Kˣ) s (fun _ => 1)

theorem sourceKPCuspResidualFrequencyScale_ne_zero (m : Kˣ) (s : ℂ) :
    sourceKPCuspResidualFrequencyScale K hζ m s ≠ 0 := by
  classical
  unfold sourceKPCuspResidualFrequencyScale
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  have hv : 0 < ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ :=
    norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hv.ne'))

theorem sourceKPCuspResidualFrequencyScale_analyticAt (m : Kˣ) (s : ℂ) :
    AnalyticAt ℂ (sourceKPCuspResidualFrequencyScale K hζ m) s := by
  classical
  unfold sourceKPCuspResidualFrequencyScale
  refine Finset.analyticAt_fun_prod _ (fun v _ => ?_)
  have hv : 0 < ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ :=
    norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hv.ne')]
  fun_prop

theorem sourceKPCuspResidualUnitArchValue_analyticOnNhd :
    AnalyticOnNhd ℂ (sourceKPCuspResidualUnitArchValue K hζ) {s : ℂ | 0 < s.re} :=
  sourceKPTraceJacquetArchProfile_analyticOnNhd K hζ 1 (fun _ => 1) (fun _ => zero_lt_one)

theorem sourceKPCuspResidualUnitArchValue_oneSixth_ne_zero :
    sourceKPCuspResidualUnitArchValue K hζ (1/6) ≠ 0 := by
  have h := (sourceKPTraceJacquetArchProfile_oneSixth_positive K hζ 1 (fun _ => 1)
    (fun _ => zero_lt_one)).1
  intro hz
  change 0 < (sourceKPCuspResidualUnitArchValue K hζ (1/6)).re at h
  rw [hz,Complex.zero_re] at h
  exact (lt_irrefl (0 : ℝ)) h

/-- Initial-region covariance of the genuine finite Jacquet integral,
with the common archimedean factor kept on both sides. -/
theorem sourceKPCuspResidualUnit_initial (m : Kˣ) (qf : Gf) {s : ℂ}
    (hs : ((3*(Module.finrank ℚ K+1):ℕ):ℝ) ≤ 2*s.re+1) :
    sourceKPCuspResidualUnitArchValue K hζ s*sourceKPCuspResidualFrequencyScale K hζ m s*
      (∫ z, sourceKPTraceJacquetFiniteKernel K hζ m s qf z ∂sourceKPFiniteStandardHaar K) =
    sourceKPCuspResidualUnitArchValue K hζ s*
      (∫ z, sourceKPTraceJacquetFiniteKernel K hζ 1 s
        (sourceKPCuspResidualUnitTranslate K hζ m qf) z ∂sourceKPFiniteStandardHaar K) := by
  let y : InfinitePlace K → ℝ := fun v => ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖⁻¹
  have hn (v : InfinitePlace K) : 0 < ‖(sourceKPCuspRationalComplexUnit K hζ m v : ℂ)‖ :=
    norm_pos_iff.mpr (sourceKPCuspRationalComplexUnit K hζ m v).ne_zero
  have hy (v : InfinitePlace K) : 0 < y v := inv_pos.mpr (hn v)
  have hy1 : sourceKPCuspRationalHeight K hζ m y = fun _ => 1 := by
    funext v
    exact mul_inv_cancel₀ (hn v).ne'
  have hs₀ : 0 < s.re := by
    have hdeg : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
    push_cast at hs
    linarith
  have h := sourceKPAdelicCompactEisenstein_traceJacquet_positive_height K hζ hs m y hy qf
  rw [sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite K hζ hs m
      (sourceKPCuspHeightSection K hζ y hy,qf),
    sourceKPAdelicCompactEisenstein_traceJacquet_arch_finite K hζ hs 1
      (sourceKPCuspHeightSection K hζ (sourceKPCuspRationalHeight K hζ m y)
          (sourceKPCuspRationalHeight_pos K hζ m y hy),
        (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2 * qf)] at h
  rw [sourceKPCuspHeightSection_arch_jacquet K hζ hs₀ m y hy,
    sourceKPCuspHeightSection_arch_jacquet K hζ hs₀ 1 (sourceKPCuspRationalHeight K hζ m y)
      (sourceKPCuspRationalHeight_pos K hζ m y hy),
    sourceKPTraceJacquetArchProfile_frequency_scale K hζ m s y hy] at h
  simp only [hy1] at h
  change (sourceKPCuspResidualFrequencyScale K hζ m s*sourceKPCuspResidualUnitArchValue K hζ s)*_ =
    sourceKPCuspResidualUnitArchValue K hζ s*_ at h
  simpa only [sourceKPCuspResidualUnitTranslate,
    mul_comm (sourceKPCuspResidualFrequencyScale K hζ m s)
    (sourceKPCuspResidualUnitArchValue K hζ s)] using h

end
end ArtinMatthews
