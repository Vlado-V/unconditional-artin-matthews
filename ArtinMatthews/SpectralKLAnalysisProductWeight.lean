module

public import ArtinMatthews.SpectralKLAnalysisIntegral
public import ArtinMatthews.SpectralKLAnalysisCalibration
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual compact-test KL coefficients absorb the O(1/t) spectral
edge majorant.  At infinity L2 Plancherel gives the required L1 product. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectralKL_L2_norm_product_integrable (F G : ℝ → ℂ)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    Integrable (fun t : ℝ => ‖F t‖*‖G t‖) spectralKLSpectralMeasure := by
  have hi := (L2.integrable_inner (𝕜 := ℂ) (hF.toLp F) (hG.toLp G)).norm
  apply hi.congr
  filter_upwards [hF.coeFn_toLp,hG.coeFn_toLp] with t htF htG
  rw [RCLike.inner_apply,htF,htG,norm_mul]
  change ‖G t‖*‖star (F t)‖ = ‖F t‖*‖G t‖
  rw [norm_star]
  ring_nf

theorem spectralKL_continuous_L2_product_div_integrable (F G : ℝ → ℂ)
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) :
    Integrable (fun t : ℝ => (‖F t‖*‖G t‖)/t) spectralKLSpectralMeasure := by
  let P : ℝ → ℝ := fun t => ‖F t‖*‖G t‖
  let H : ℝ → ℝ := fun t => (2/Real.pi^2)*Real.sinh (Real.pi*t)*P t
  have hP : Integrable P spectralKLSpectralMeasure := spectralKL_L2_norm_product_integrable F G hF hG
  have hcH : Continuous H := by dsimp [H,P]; fun_prop
  have hHI : Integrable ((Ioc (0 : ℝ) 1).indicator H) volume := by
    apply (integrable_indicator_iff measurableSet_Ioc).mpr
    exact hcH.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hsmall : Integrable ((Ioc (0 : ℝ) 1).indicator (fun t => P t/t)) spectralKLSpectralMeasure := by
    apply (spectralKLPositiveWeightMeasure_integrable_iff spectralKLPlancherelWeight _
      spectralKLPlancherelWeight_continuous.measurable
      (fun t ht => (spectralKLPlancherelWeight_pos ht).le)).mpr
    apply hHI.restrict.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    by_cases ht1 : t ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_mem ht1,indicator_of_mem ht1]
      dsimp [H,spectralKLPlancherelWeight]
      field_simp [ht.ne',Real.pi_ne_zero]
    · simp only [indicator_of_notMem ht1,mul_zero]
  have htail : Integrable ((Ioi (1 : ℝ)).indicator (fun t => P t/t)) spectralKLSpectralMeasure := by
    apply (integrable_indicator_iff measurableSet_Ioi).mpr
    have hm : Measurable (fun t : ℝ => P t/t) := by dsimp [P]; fun_prop
    apply hP.restrict.mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 1 < t at ht
    have ht0 : 0 < t := by linarith
    have hPn : 0 ≤ P t := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hPn ht0.le)]
    exact div_le_self hPn (by linarith)
  apply (hsmall.add htail).congr
  filter_upwards [spectralKLPositiveWeightMeasure_ae_pos spectralKLPlancherelWeight] with t ht
  dsimp only [Pi.add_apply]
  by_cases ht1 : t ≤ 1
  · rw [indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht,ht1⟩),
      indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht1),add_zero]
  · have htgt : 1 < t := lt_of_not_ge ht1
    rw [indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => ht1 h.2),
      indicator_of_mem (show t ∈ Ioi (1 : ℝ) from htgt),zero_add]

theorem spectralKL_continuous_L2_product_order_weight_integrable (F G : ℝ → ℂ)
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : MemLp F 2 spectralKLSpectralMeasure) (hG : MemLp G 2 spectralKLSpectralMeasure) (C : ℝ) :
    Integrable (fun t : ℝ => ‖F t‖*‖G t‖*(1+C/t)) spectralKLSpectralMeasure := by
  have h1 := spectralKL_L2_norm_product_integrable F G hF hG
  have h2 := (spectralKL_continuous_L2_product_div_integrable F G hcF hcG hF hG).const_mul C
  apply (h1.add h2).congr
  exact Filter.Eventually.of_forall (fun t => by dsimp only [Pi.add_apply]; ring)

theorem spectralKL_compact_analysis_order_weight_integrable (f g : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfp : tsupport f ⊆ Ioi (0 : ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ)) (C : ℝ) :
    Integrable (fun t : ℝ => ‖spectralKLPhysicalAnalysisIntegral f t‖*
      ‖spectralKLPhysicalAnalysisIntegral g t‖*(1+C/t)) spectralKLSpectralMeasure :=
  spectralKL_continuous_L2_product_order_weight_integrable _ _
    (spectralKLPhysicalAnalysisIntegral_continuous f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_continuous g hg hgc hgp)
    (spectralKLPhysicalAnalysisIntegral_memLp f hf hfc hfp)
    (spectralKLPhysicalAnalysisIntegral_memLp g hg hgc hgp) C

end ArtinMatthews
