module

public import ArtinMatthews.SourceKPExteriorRadialCore
public import ArtinMatthews.MeasurableParametricDerivative
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus


set_option backward.privateInPublic true
@[expose] public section

/-! Differentiate the actual restricted automorphic norm along the common radial flow. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter Set MeasureTheory
open scoped NumberField MatrixGroups AdeleRing ENNReal RealInnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPExteriorCoreNormDerivative (f : sourceKPCompactC2Core K hζ) (t T : ℝ)
    (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) : ℝ :=
  2 * ⟪sourceKPExteriorCoreValue K hζ f t T hT q,
    sourceKPExteriorCoreRadialDerivative K hζ f t T hT q⟫

theorem sourceKPExteriorCoreNormSq_hasDerivAt (f : sourceKPCompactC2Core K hζ)
    (t T : ℝ) (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    HasDerivAt (fun s => ‖sourceKPExteriorCoreValue K hζ f s T hT q‖^2)
      (sourceKPExteriorCoreNormDerivative K hζ f t T hT q) t :=
  (sourceKPExteriorCoreValue_hasDerivAt K hζ f t T hT q).norm_sq

theorem sourceKPExteriorCoreNormDerivative_integral (f : sourceKPCompactC2Core K hζ)
    (T : ℝ) (hT : 1 < T)
    (hsupp : tsupport (sourceKPExteriorCoreLift K hζ f) ⊆
      {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    Integrable (sourceKPExteriorCoreNormDerivative K hζ f 0 T hT) (sourceKPHighCuspMeasure K hζ T) ∧
      (∫ q, sourceKPExteriorCoreNormDerivative K hζ f 0 T hT q ∂sourceKPHighCuspMeasure K hζ T) =
        (2 * (InfinitePlace.nrComplexPlaces K : ℝ)) *
          ∫ x, ‖sourceKPExteriorCoreLift K hζ f x‖^2
            ∂sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ) := by
  let μ := sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
  let μH := sourceKPHighCuspMeasure K hζ T
  let u := sourceKPExteriorCoreLift K hζ f
  let E := sourceKPExteriorCoreEnergyLift K hζ f
  let F : ℝ → SourceKPHighCuspAutomorphic K hζ T → ℝ :=
    fun t q => ‖sourceKPExteriorCoreValue K hζ f t T hT q‖^2
  let D := fun t => sourceKPExteriorCoreNormDerivative K hζ f t T hT
  let r : ℝ := InfinitePlace.nrComplexPlaces K
  let M := ∫ x, ‖u x‖^2 ∂μ
  have hu : Continuous u := sourceKPExteriorCoreLift_continuous K hζ f
  have huc : HasCompactSupport u := sourceKPExteriorCoreLift_hasCompactSupport K hζ f
  obtain ⟨s,hs,C,hC,hHull⟩ := sourceKPExteriorRadial_compact_hull K hζ T hT huc hsupp
  obtain ⟨B,hB⟩ := hu.norm.bddAbove_range_of_hasCompactSupport huc.norm
  obtain ⟨B',hB'⟩ := (sourceKPCompactCoreEnergy_continuous K hζ f).bddAbove_range_of_hasCompactSupport
    (sourceKPCompactCoreEnergy_hasCompactSupport K hζ f)
  let B₁ := max B 0
  let B₂ := max B' 0
  have hB₁ : 0 ≤ B₁ := le_max_right _ _
  have hB₂ : 0 ≤ B₂ := le_max_right _ _
  have hr : 0 ≤ r := Nat.cast_nonneg _
  have hu_bound (x : SourceKPAutomorphicLevel K hζ) : ‖u x‖ ≤ B₁ :=
    (hB (mem_range_self x)).trans (le_max_left _ _)
  have hE_bound (x : SourceKPAutomorphicLevel K hζ) : E x ≤ B₂ :=
    (hB' (mem_range_self (sourceKPAutomorphicCompactMk K hζ x))).trans (le_max_left _ _)
  let L := 2*B₁*Real.sqrt (r*B₂)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let A : Set (SourceKPHighCuspAutomorphic K hζ T) := Subtype.val ⁻¹' C
  have hA : MeasurableSet A := hC.isClosed.measurableSet.preimage measurable_subtype_coe
  let : IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)) :=
    sourceKPAutomorphicMeasure_finiteOnCompacts K hζ _
  have hAfinite : μH A < ∞ := by
    change sourceKPHighCuspMeasure K hζ T A < ∞
    rw [sourceKPHighCuspMeasure_apply]
    apply lt_of_le_of_lt (measure_mono ?_) hC.measure_lt_top
    rintro _ ⟨q,hq,rfl⟩
    exact hq
  let bound : SourceKPHighCuspAutomorphic K hζ T → ℝ := A.indicator (fun _ => L)
  have hboundInt : Integrable bound μH :=
    (integrable_indicator_iff hA).mpr (integrableOn_const hAfinite.ne)
  have hFmeas (t : ℝ) : Measurable (F t) :=
    (sourceKPExteriorCoreValue_measurable K hζ f t T hT).norm.pow_const 2
  have hD (t : ℝ) (q : SourceKPHighCuspAutomorphic K hζ T) :
      HasDerivAt (fun s => F s q) (D t q) t :=
    sourceKPExteriorCoreNormSq_hasDerivAt K hζ f t T hT q
  have hDmeas : Measurable (D 0) := sourceMeasurable_parametric_derivative_zero F (D 0) hFmeas (hD 0)
  have hFint : Integrable (F 0) μH := by
    have hI : Integrable (fun x => ‖u x‖^2) (μ.restrict {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :=
      (sourceKPExteriorCoreLift_normSq_integrable K hζ f).restrict
    have h := (sourceKPHighCuspMeasure_val_preserving K hζ T).integrable_comp_of_integrable hI
    simpa only [F, Function.comp_def, sourceKPExteriorCoreValue_zero] using h
  have hbound (q : SourceKPHighCuspAutomorphic K hζ T) (t : ℝ) (ht : t ∈ s) :
      ‖D t q‖ ≤ bound q := by
    by_cases hz : sourceKPExteriorCoreValue K hζ f t T hT q = 0
    · have hd0 : D t q = 0 := by simp [D, sourceKPExteriorCoreNormDerivative,hz]
      by_cases hq : q ∈ A <;> simp [bound,hq,hd0,hL]
    · have hq : q ∈ A := hHull t ht q hz
      rw [show bound q = L from indicator_of_mem hq _]
      have hV : ‖sourceKPExteriorCoreValue K hζ f t T hT q‖ ≤ B₁ := hu_bound _
      have hDeriv : ‖sourceKPExteriorCoreRadialDerivative K hζ f t T hT q‖ ≤ Real.sqrt (r*B₂) :=
        Real.le_sqrt_of_sq_le ((sourceKPExteriorCoreRadialDerivative_normSq_le K hζ f t T hT q).trans
          (mul_le_mul_of_nonneg_left (hE_bound _) hr))
      change ‖2 * ⟪sourceKPExteriorCoreValue K hζ f t T hT q,
        sourceKPExteriorCoreRadialDerivative K hζ f t T hT q⟫‖ ≤ L
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
      calc
        _ ≤ 2 * (‖sourceKPExteriorCoreValue K hζ f t T hT q‖ *
            ‖sourceKPExteriorCoreRadialDerivative K hζ f t T hT q‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
        _ ≤ 2*(B₁*Real.sqrt (r*B₂)) := mul_le_mul_of_nonneg_left
          (mul_le_mul hV hDeriv (norm_nonneg _) hB₁) (by norm_num)
        _ = L := (mul_assoc _ _ _).symm
  obtain ⟨hDint,hInt⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Filter.Eventually.of_forall (fun t => (hFmeas t).aestronglyMeasurable)) hFint
    hDmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound) hboundInt
    (Filter.Eventually.of_forall (fun q t _ => hD t q))
  have hnear : (fun t => ∫ q, F t q ∂μH) =ᶠ[𝓝 0]
      (fun t => sourceKPRadialHeightScale K t * M) :=
    sourceKPExteriorRadial_normSq_integral_eventually K hζ T hT hu huc hsupp
  have hscale : HasDerivAt (sourceKPRadialHeightScale K) (2*r) 0 := by
    have he : sourceKPRadialHeightScale K = fun t => Real.exp (2*r*t) :=
      funext (sourceKPRadialHeightScale_eq_nrComplex K hζ)
    rw [he]
    have hlin : HasDerivAt (fun t : ℝ => (2*r)*t) (2*r) 0 := by
      simpa only [mul_one] using! (hasDerivAt_id (0 : ℝ)).const_mul (2*r)
    have h := (Real.hasDerivAt_exp ((2*r)*0)).comp 0 hlin
    simpa only [Function.comp_def,mul_zero,Real.exp_zero,one_mul] using h
  have hscaled := (hscale.mul_const M).congr_of_eventuallyEq hnear
  exact ⟨hDint,hInt.unique hscaled⟩

end
end ArtinMatthews
