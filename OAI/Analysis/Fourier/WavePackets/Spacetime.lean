module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.Fourier.WavePackets.Young
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convolution
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

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ENNReal

/-- On a probability parameter space, a uniform bound for the spatial
`Lᵖ` norm is also a bound for the product-space `Lᵖ` norm. -/
theorem eLpNorm_prod_le_of_slice_bound {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {ν : Measure A} {μ : Measure B} [SFinite ν] [SFinite μ]
    (hmass : ν Set.univ = 1) {F : A × B → ℂ}
    (hF : AEStronglyMeasurable F (ν.prod μ)) {p : ℝ≥0∞}
    (hp₀ : p ≠ 0) (hp_top : p ≠ ∞) {C : ℝ≥0∞}
    (hb : ∀ᵐ t ∂ν, eLpNorm (fun x => F (t, x)) p μ ≤ C) :
    eLpNorm F p (ν.prod μ) ≤ C := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hF,
    lintegral_prod _ (hF.enorm.pow_const p.toReal)]
  have hs : (∫⁻ t, ∫⁻ x, ‖F (t, x)‖ₑ ^ p.toReal ∂μ ∂ν) ≤ C ^ p.toReal := by
    calc
      _ ≤ ∫⁻ _t, C ^ p.toReal ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hb, hF.prodMk_left] with t ht htm
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top htm] at ht
        have htp := ENNReal.rpow_le_rpow ht hpr.le
        simpa only [← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one] using htp
      _ = _ := by rw [lintegral_const, hmass, mul_one]
  have hsp := ENNReal.rpow_le_rpow hs (show 0 ≤ 1 / p.toReal by positivity)
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hpr.ne', ENNReal.rpow_one] using hsp

section WaveTail

open scoped ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] in
theorem continuous_semiclassicalWaveKernel_spacetime {a : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ) :
    Continuous (fun q : ℝ × E => semiclassicalWaveKernel μ a h q.1 q.2) := by
  apply continuous_const.mul
  apply continuous_of_dominated (bound := fun ξ => ‖a ξ‖)
  · intro q
    apply Continuous.aestronglyMeasurable
    exact (continuous_oscillation (by unfold euclideanWavePhase; fun_prop) h).mul ha
  · intro q
    exact Filter.Eventually.of_forall fun ξ => by simp [norm_oscillation]
  · exact (ha.integrable_of_hasCompactSupport hs).norm
  · apply Filter.Eventually.of_forall
    intro ξ
    unfold oscillation euclideanWavePhase
    fun_prop

omit [FiniteDimensional ℝ E] in
theorem measurable_waveTail_spacetime {a : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ) :
    Measurable (fun q : ℝ × E => waveTail μ a h q.1 q.2) := by
  have heq : (fun q : ℝ × E => waveTail μ a h q.1 q.2) =
      {q : ℝ × E | 3 ≤ ‖q.2‖}.indicator
        (fun q => semiclassicalWaveKernel μ a h q.1 q.2) := by
    funext q
    by_cases hq : 3 ≤ ‖q.2‖ <;> simp [waveTail, Set.indicator, hq]
  rw [heq]
  apply (continuous_semiclassicalWaveKernel_spacetime ha hs h).measurable.indicator
  exact measurableSet_le measurable_const (measurable_norm.comp measurable_snd)

theorem stronglyMeasurable_waveTail_convolution_spacetime_of_measurable {a f : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ) (hf : Measurable f) :
    StronglyMeasurable (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2) := by
  have hm : StronglyMeasurable (fun q : (ℝ × E) × E =>
      waveTail μ a h q.1.1 q.2 * f (q.1.2 - q.2)) := by
    apply Measurable.stronglyMeasurable
    exact ((measurable_waveTail_spacetime ha hs h).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (hf.comp ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact hm.integral_prod_right'

theorem stronglyMeasurable_waveTail_convolution_spacetime {a f : E → ℂ}
    (ha : Continuous a) (hs : HasCompactSupport a) (h : ℝ)
    (hf : AEStronglyMeasurable f μ) :
    StronglyMeasurable (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2) := by
  have heq : (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2) =
      (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) (hf.mk f) μ q.2) := by
    funext q
    exact congrFun (convolution_congr (ContinuousLinearMap.mul ℂ ℂ)
      (Filter.EventuallyEq.rfl : waveTail μ a h q.1 =ᵐ[μ] waveTail μ a h q.1) hf.ae_eq_mk) q.2
  rw [heq]
  exact stronglyMeasurable_waveTail_convolution_spacetime_of_measurable ha hs h
    hf.stronglyMeasurable_mk.measurable

/-- The full space-time version on `[1,2]` of the negligible far-input
operator estimate used in the Euclidean transfer. -/
theorem waveTail_convolution_spacetime_bound {a : E → ℂ}
    (ha : ContDiff ℝ ∞ a) (hzero : (0 : E) ∉ tsupport a)
    (hs : HasCompactSupport a) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∀ (f : E → ℂ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → MemLp f p μ →
        MemLp (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2)
          p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod μ) ∧
        eLpNorm (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2)
          p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod μ) ≤
          ENNReal.ofReal (C * h ^ N) * eLpNorm f p μ := by
  obtain ⟨C, hC, hb⟩ := waveTail_convolution_eLpNorm_bound (μ := μ) ha hzero hs N
  refine ⟨C, hC, ?_⟩
  intro h hh hh₁ f p hp hp_top hf
  have hp₀ : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hbound : eLpNorm (fun q : ℝ × E => complexConvolution (waveTail μ a h q.1) f μ q.2)
      p ((volume.restrict (Set.Icc (1 : ℝ) 2)).prod μ) ≤
      ENNReal.ofReal (C * h ^ N) * eLpNorm f p μ := by
    apply eLpNorm_prod_le_of_slice_bound (by norm_num [Real.volume_Icc])
      (stronglyMeasurable_waveTail_convolution_spacetime ha.continuous hs h
        hf.aestronglyMeasurable).aestronglyMeasurable hp₀ hp_top
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact (hb T h (by linarith [hT.1]) hT.2 hh hh₁ f p hp hp_top hf).2
  exact ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top), hbound⟩

end WaveTail

end OAI.Analysis.Fourier.WavePackets
