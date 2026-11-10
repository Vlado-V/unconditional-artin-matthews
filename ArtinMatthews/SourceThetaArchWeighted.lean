module

public import ArtinMatthews.SourceSLocalOtherTensor
public import ArtinMatthews.SourceSLocalWholeMellin
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual complex-place weighted L1 and supremum estimates for
the two-ended source03 condition. Both are taken in the exact polar Haar. -/
namespace ArtinMatthews.SourceReflection

open NumberField NumberField.InfinitePlace MeasureTheory Set Filter
open ArtinMatthews.SourcePhysical
open scoped NumberField Classical ArtinMatthews.SourcePhysical
noncomputable section

theorem sourceThetaLogFactor_weighted {g : Circle → ℝ → ℂ} {δ σ : ℝ} (hσ : -δ < σ)
    (hb : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ θ t,
      ‖g θ t‖ ≤ C * min (Real.exp (δ * t)) (Real.exp (-A * t))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ t, ‖g θ t‖ ≤ C * Real.exp (-σ * t) := by
  let A := max 1 σ
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨C, hC, h⟩ := hb A hA
  refine ⟨C, hC, fun θ t => (h θ t).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  rcases le_total t 0 with ht | ht
  · exact (min_le_left _ _).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_right (by linarith) ht))
  · exact (min_le_right _ _).trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (neg_le_neg (le_max_right _ _)) ht))

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (v : InfinitePlace K)

local notation "hv" => sourceSLocalComplexPlace K hζ v

theorem sourceThetaArchNorm_at_polar (p : Circle × Multiplicative ℝ) :
    sourceSheetArchNorm v (sourceSLocalPolarPlace hv p) = Real.exp p.2.toAdd := by
  rw [sourceSheetArchNorm_eq_complex hv]
  change ‖((sourceComplexPlaceUnitsEquiv hv
    ((sourceComplexPlaceUnitsEquiv hv).symm (sourceComplexUnitPolarMulEquiv p)) : ℂˣ) : ℂ)‖ ^ 2 = _
  rw [ContinuousMulEquiv.apply_symm_apply]
  change ‖((sourceComplexRadialUnit p.2.toAdd * Circle.toUnits p.1 : ℂˣ) : ℂ)‖ ^ 2 = _
  rw [sourceComplexRadialUnit_mul_angle_norm, pow_two, ← Real.exp_add]
  congr 1
  ring

theorem sourceThetaArchFactor_weighted_integrable (f : v.Completionˣ → ℂ) (hf : Measurable f)
    {δ σ : ℝ} (hσ : -δ < σ)
    (hb : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ z,
      ‖f z‖ ≤ C * min ((sourceSheetArchNorm v z) ^ δ) ((sourceSheetArchNorm v z) ^ (-A))) :
    Integrable (fun z => ‖f z‖ * (sourceSheetArchNorm v z) ^ σ) (sourceSLocalArchUnitMeasure K hζ v) := by
  let A := max 1 (σ + 1)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hAσ : σ - A < 0 := by linarith [le_max_right (1 : ℝ) (σ + 1)]
  obtain ⟨C, hC, h⟩ := hb A hA
  let W (t : ℝ) := (Iic 0).indicator (fun t => Real.exp ((δ + σ) * t)) t +
    (Ioi 0).indicator (fun t => Real.exp ((σ - A) * t)) t
  have hW : Integrable W :=
    ((integrableOn_exp_mul_Iic (a := δ + σ) (by linarith) 0).integrable_indicator measurableSet_Iic).add
      ((integrableOn_exp_mul_Ioi hAσ 0).integrable_indicator measurableSet_Ioi)
  let F (z : v.Completionˣ) := ‖f z‖ * (sourceSheetArchNorm v z) ^ σ
  have hW' : Integrable (fun p : Circle × Multiplicative ℝ => C * W p.2.toAdd)
      (sourceCircleHaar.prod sourceRealLogHaar) := (hW.const_mul C).comp_snd sourceCircleHaar
  have hc : Continuous (sourceSheetArchNorm v) := by
    unfold sourceSheetArchNorm
    exact (continuous_norm.comp Units.continuous_val).pow 2
  have hm : Measurable F := hf.norm.mul
    (hc.rpow_const (fun z => Or.inl (sourceSheetArchNorm_pos v z).ne')).measurable
  have hp := sourceSLocalPolarPlace_measurable hv
  rw [sourceSLocalArchUnitMeasure_eq_polar K hζ v]
  apply (integrable_map_measure hm.aestronglyMeasurable hp.aemeasurable).mpr
  apply hW'.mono' (hm.comp hp).aestronglyMeasurable
  filter_upwards with p
  let t := p.2.toAdd
  let z := sourceSLocalPolarPlace hv p
  have hz : sourceSheetArchNorm v z = Real.exp t := sourceThetaArchNorm_at_polar K hζ v p
  change ‖‖f z‖ * (sourceSheetArchNorm v z) ^ σ‖ ≤ C * W t
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (sourceSheetArchNorm_pos v z).le σ)), hz]
  have hpt := h z
  rw [hz] at hpt
  have he (a : ℝ) : (Real.exp t) ^ a = Real.exp (a * t) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm]
  rw [he δ, he (-A)] at hpt
  rw [he σ]
  rcases le_or_gt t 0 with ht | ht
  · have hleft := hpt.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    calc
      _ ≤ (C * Real.exp (δ * t)) * Real.exp (σ * t) :=
        mul_le_mul_of_nonneg_right hleft (Real.exp_pos _).le
      _ = _ := by
        dsimp only [W]
        rw [indicator_of_mem (mem_Iic.mpr ht),
          indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht), add_zero,
          mul_assoc, ← Real.exp_add, add_mul]
  · have hright := hpt.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
    calc
      _ ≤ (C * Real.exp (-A * t)) * Real.exp (σ * t) :=
        mul_le_mul_of_nonneg_right hright (Real.exp_pos _).le
      _ = _ := by
        dsimp only [W]
        rw [indicator_of_notMem (show t ∉ Iic (0 : ℝ) from not_le.mpr ht),
          indicator_of_mem (mem_Ioi.mpr ht), zero_add,
          mul_assoc, ← Real.exp_add]
        congr 2
        ring

end
end ArtinMatthews.SourceReflection
