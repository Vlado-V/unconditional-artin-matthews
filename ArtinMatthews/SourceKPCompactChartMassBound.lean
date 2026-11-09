module

public import ArtinMatthews.SourceKPCompactChartMassLift
public import ArtinMatthews.L2MeasurableCutoff


set_option backward.privateInPublic true
@[expose] public section

/-! Bounded chart pullback with the exact finite stabilizer factor. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Filter Set
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)

local notation "X" => ProductSpace (InfinitePlace K)
local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "U" => sourceKPFiniteChartCoordinateDomain K hζ b p
local notation "R" => Set.range (sourceKPFiniteChartProjection K hζ b p)
local notation "H" => SourceKPFiniteChartStabilizer K hζ b p
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)

theorem sourceKPCompactCoordinateProjection_ae_chart {P : Y → Prop}
    (h : ∀ᵐ y ∂μ, P y) :
    ∀ᵐ x ∂ν, x ∈ U → P (sourceKPCompactCoordinateProjection K hζ b x) := by
  have hr : ∀ᵐ y ∂((μ).restrict R), P y := ae_restrict_of_ae h
  have hp := (sourceKPCompactCoordinateProjection_measurePreserving K hζ b p).quasiMeasurePreserving.ae hr
  have hc : (Nat.card H : ℝ≥0∞)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  exact (ae_restrict_iff' (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet).mp
    ((Measure.ae_ennreal_smul_measure_iff hc).mp hp)

theorem sourceKPCompactChartMassLift_norm_sq_le (g : Lp ℂ 2 μ) :
    ‖(sourceKPCompactChartMassLift K hζ b p g).val‖ ^ 2 ≤ (Nat.card H : ℝ) * ‖g‖ ^ 2 := by
  let q := sourceKPCompactCoordinateProjection K hζ b
  let n : ℝ≥0∞ := Nat.card H
  let f : Y → ℝ := fun y => ‖g y‖ ^ 2
  have hu := (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p).measurableSet
  have hg : Integrable f μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hgr : Integrable f ((μ).restrict R) := hg.restrict
  have hMP := sourceKPCompactCoordinateProjection_measurePreserving K hζ b p
  have hm : Measure.map q (n⁻¹ • (ν).restrict U) = (μ).restrict R := hMP.map_eq
  have hI : (∫ x, f (q x) ∂(n⁻¹ • (ν).restrict U)) = ∫ y in R, f y ∂μ := by
    rw [← hm]
    exact (integral_map hMP.measurable.aemeasurable
      (hm.symm ▸ hgr.aestronglyMeasurable)).symm
  have hn : n.toReal ≠ 0 := by
    rw [show n.toReal = (Nat.card H : ℝ) from ENNReal.toReal_natCast _]
    exact_mod_cast (Nat.card_pos.ne' : Nat.card H ≠ 0)
  calc
    _ = ∫ x in U, f (q x) ∂ν := by
      rw [heightL2_norm_sq_integral ν, ← integral_indicator hu]
      apply integral_congr_ae
      filter_upwards [sourceKPCompactChartMassLift_coe K hζ b p g] with x hx
      rw [hx]
      by_cases hxu : x ∈ U
      · simp only [Set.indicator_of_mem hxu, Function.comp_apply, q, f]
      · simp only [Set.indicator_of_notMem hxu, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    _ = n.toReal * ∫ x, f (q x) ∂(n⁻¹ • (ν).restrict U) := by
      rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hn, one_mul]
    _ = n.toReal * ∫ y in R, f y ∂μ := congrArg (fun t => n.toReal * t) hI
    _ ≤ n.toReal * ‖g‖ ^ 2 := by
      rw [heightL2_norm_sq_integral μ]
      exact mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall (fun y => sq_nonneg ‖g y‖)) hg)
        ENNReal.toReal_nonneg
    _ = _ := by simp only [n, ENNReal.toReal_natCast]

def sourceKPCompactChartMassLiftCLM : Lp ℂ 2 μ →L[ℂ] H1Mass (InfinitePlace K) := by
  let L : Lp ℂ 2 μ →ₗ[ℂ] H1Mass (InfinitePlace K) :=
    { toFun := fun g => (sourceKPCompactChartMassLift K hζ b p g).val
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [sourceKPCompactChartMassLift_coe K hζ b p (f + g),
          sourceKPCompactChartMassLift_coe K hζ b p f, sourceKPCompactChartMassLift_coe K hζ b p g,
          Lp.coeFn_add (sourceKPCompactChartMassLift K hζ b p f).val
            (sourceKPCompactChartMassLift K hζ b p g).val,
          sourceKPCompactCoordinateProjection_ae_chart K hζ b p (Lp.coeFn_add f g)]
          with x hfg hf hg hadd hq
        change (sourceKPCompactChartMassLift K hζ b p (f + g)).val x =
          ((sourceKPCompactChartMassLift K hζ b p f).val +
            (sourceKPCompactChartMassLift K hζ b p g).val) x
        rw [hfg, hadd, Pi.add_apply, hf, hg]
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx, Function.comp_apply, hq hx, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, zero_add]
      map_smul' := by
        intro c g
        apply Lp.ext
        filter_upwards [sourceKPCompactChartMassLift_coe K hζ b p (c • g),
          sourceKPCompactChartMassLift_coe K hζ b p g,
          Lp.coeFn_smul c (sourceKPCompactChartMassLift K hζ b p g).val,
          sourceKPCompactCoordinateProjection_ae_chart K hζ b p (Lp.coeFn_smul c g)]
          with x hcg hg hsmul hq
        change (sourceKPCompactChartMassLift K hζ b p (c • g)).val x =
          (c • (sourceKPCompactChartMassLift K hζ b p g).val) x
        rw [hcg, hsmul, Pi.smul_apply, hg]
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx, Function.comp_apply, hq hx, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
  refine L.mkContinuous (Real.sqrt (Nat.card H : ℝ)) (fun g => ?_)
  change ‖(sourceKPCompactChartMassLift K hζ b p g).val‖ ≤ Real.sqrt (Nat.card H : ℝ) * ‖g‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact sourceKPCompactChartMassLift_norm_sq_le K hζ b p g

theorem sourceKPCompactChartMassLiftCLM_apply (g : Lp ℂ 2 μ) :
    sourceKPCompactChartMassLiftCLM K hζ b p g = (sourceKPCompactChartMassLift K hζ b p g).val := rfl

theorem sourceKPCompactChartMassLiftCLM_coe (g : Lp ℂ 2 μ) :
    (sourceKPCompactChartMassLiftCLM K hζ b p g : X → ℂ) =ᵐ[ν]
      (U).indicator (g ∘ sourceKPCompactCoordinateProjection K hζ b) :=
  sourceKPCompactChartMassLift_coe K hζ b p g

end
end ArtinMatthews
