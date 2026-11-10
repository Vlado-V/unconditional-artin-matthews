module

public import ArtinMatthews.SpectralKLWeightedMeasures
public import ArtinMatthews.SpectralWeylMultipliers
public import ArtinMatthews.SpectralWeylBoundedOrder
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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

/-! A bounded positive-line spectral kernel defines a continuous pairing
on the actual KL L2 space. This supplies the spectral side of height
cutoff passage without a pointwise inverse hypothesis. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
namespace ArtinMatthews

theorem spectralKLBoundedKernel_memLp (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (G : Lp ℂ 2 spectralKLSpectralMeasure) :
    MemLp (fun t => star (M t)*G t) 2 spectralKLSpectralMeasure := by
  apply (Lp.memLp G).of_le_mul (c := C)
    (((continuous_star.measurable.comp hM).aestronglyMeasurable).mul (Lp.aestronglyMeasurable G))
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
  change ‖star (M t)*G t‖ ≤ C*‖G t‖
  rw [norm_mul,norm_star]
  exact mul_le_mul_of_nonneg_right (hb t ht) (norm_nonneg _)

def spectralKLBoundedKernelVector (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (G : Lp ℂ 2 spectralKLSpectralMeasure) :
    Lp ℂ 2 spectralKLSpectralMeasure :=
  (spectralKLBoundedKernel_memLp M hM C hb G).toLp _

theorem spectralKLBoundedKernel_inner (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (F G : Lp ℂ 2 spectralKLSpectralMeasure) :
    inner ℂ (spectralKLBoundedKernelVector M hM C hb G) F =
      ∫ t, M t*F t*star (G t) ∂spectralKLSpectralMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(spectralKLBoundedKernel_memLp M hM C hb G).coeFn_toLp] with t ht
  change (spectralKLBoundedKernelVector M hM C hb G) t = star (M t)*G t at ht
  change inner ℂ ((spectralKLBoundedKernelVector M hM C hb G) t) (F t) = _
  rw [RCLike.inner_apply,ht,map_mul]
  change F t*(star (star (M t))*star (G t)) = _
  rw [star_star]
  ring

theorem spectralKLBoundedKernel_pair_integrable (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (F G : Lp ℂ 2 spectralKLSpectralMeasure) :
    Integrable (fun t => M t*F t*star (G t)) spectralKLSpectralMeasure := by
  apply (L2.integrable_inner (𝕜 := ℂ) (spectralKLBoundedKernelVector M hM C hb G) F).congr
  filter_upwards [(spectralKLBoundedKernel_memLp M hM C hb G).coeFn_toLp] with t ht
  change (spectralKLBoundedKernelVector M hM C hb G) t = star (M t)*G t at ht
  change inner ℂ ((spectralKLBoundedKernelVector M hM C hb G) t) (F t) = _
  rw [RCLike.inner_apply,ht,map_mul]
  change F t*(star (star (M t))*star (G t)) = _
  rw [star_star]
  ring

theorem spectralKLBoundedKernel_pair_tendsto (M : ℝ → ℂ) (hM : Measurable M) (C : ℝ)
    (hb : ∀ t, 0 < t → ‖M t‖ ≤ C) (F : ℕ → Lp ℂ 2 spectralKLSpectralMeasure)
    (f G : Lp ℂ 2 spectralKLSpectralMeasure) (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun k => ∫ t, M t*F k t*star (G t) ∂spectralKLSpectralMeasure) atTop
      (𝓝 (∫ t, M t*f t*star (G t) ∂spectralKLSpectralMeasure)) := by
  have hc : Continuous (fun v : Lp ℂ 2 spectralKLSpectralMeasure =>
      inner ℂ (spectralKLBoundedKernelVector M hM C hb G) v) := continuous_const.inner continuous_id
  simpa only [Function.comp_def,spectralKLBoundedKernel_inner] using (hc.tendsto f).comp hF

theorem spectralWeylJ_pair_tendsto {X : ℝ} (hX : 0 < X)
    (F : ℕ → Lp ℂ 2 spectralKLSpectralMeasure) (f G : Lp ℂ 2 spectralKLSpectralMeasure)
    (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun k => ∫ t, spectralWeylJMultiplier t X*F k t*star (G t) ∂spectralKLSpectralMeasure)
      atTop (𝓝 (∫ t, spectralWeylJMultiplier t X*f t*star (G t) ∂spectralKLSpectralMeasure)) := by
  obtain ⟨C,_,hC⟩ := spectralWeylJMultiplier_bounded_positive hX
  exact spectralKLBoundedKernel_pair_tendsto _
    (spectralWeylJMultiplier_measurable.comp (measurable_id.prodMk measurable_const)) C hC F f G hF

theorem spectralWeylK_pair_tendsto {X : ℝ} (hX : 0 < X)
    (F : ℕ → Lp ℂ 2 spectralKLSpectralMeasure) (f G : Lp ℂ 2 spectralKLSpectralMeasure)
    (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun k => ∫ t, spectralWeylKMultiplier t X*F k t*star (G t) ∂spectralKLSpectralMeasure)
      atTop (𝓝 (∫ t, spectralWeylKMultiplier t X*f t*star (G t) ∂spectralKLSpectralMeasure)) := by
  obtain ⟨C,_,hC⟩ := spectralWeylKMultiplier_bounded_positive hX
  exact spectralKLBoundedKernel_pair_tendsto _
    (spectralWeylKMultiplier_measurable.comp (measurable_id.prodMk measurable_const)) C hC F f G hF

end ArtinMatthews
