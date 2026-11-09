module

public import ArtinMatthews.SourceKPExteriorRadialIBP


set_option backward.privateInPublic true
@[expose] public section

/-! The exterior Hardy threshold on the actual compact automorphic scalar core. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter Set MeasureTheory
open scoped NumberField MatrixGroups AdeleRing RealInnerProductSpace
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPExteriorCoreNormDerivative_zero_le_energy (f : sourceKPCompactC2Core K hζ)
    (T : ℝ) (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPExteriorCoreNormDerivative K hζ f 0 T hT q ≤
      (InfinitePlace.nrComplexPlaces K : ℝ) * ‖sourceKPExteriorCoreLift K hζ f q.val‖^2 +
        sourceKPExteriorCoreEnergyLift K hζ f q.val := by
  let a := sourceKPExteriorCoreLift K hζ f q.val
  let d := sourceKPExteriorCoreRadialDerivative K hζ f 0 T hT q
  let r : ℝ := InfinitePlace.nrComplexPlaces K
  have hrN : 0 < InfinitePlace.nrComplexPlaces K := by
    rw [← sourceKPRadialComplexCount K hζ]
    exact Fintype.card_pos
  have hr : 0 < r := by
    change 0 < (InfinitePlace.nrComplexPlaces K : ℝ)
    exact_mod_cast hrN
  have hd := sourceKPExteriorCoreRadialDerivative_normSq_le K hζ f 0 T hT q
  rw [sourceKPHighCuspRadialValue_zero] at hd
  change ‖d‖^2 ≤ r * sourceKPExteriorCoreEnergyLift K hζ f q.val at hd
  rw [sourceKPExteriorCoreNormDerivative,sourceKPExteriorCoreValue_zero]
  change 2 * ⟪a,d⟫ ≤ r * ‖a‖^2 + sourceKPExteriorCoreEnergyLift K hζ f q.val
  apply (mul_le_mul_iff_right₀ hr).mp
  calc
    _ = (2*r) * ⟪a,d⟫ := by ring
    _ ≤ (2*r) * (‖a‖ * ‖d‖) :=
      mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) (by positivity)
    _ ≤ r^2 * ‖a‖^2 + ‖d‖^2 := by nlinarith [sq_nonneg (r * ‖a‖ - ‖d‖)]
    _ ≤ r^2 * ‖a‖^2 + r * sourceKPExteriorCoreEnergyLift K hζ f q.val := add_le_add le_rfl hd
    _ = _ := by ring

theorem sourceKPExteriorCore_hardy (f : sourceKPCompactC2Core K hζ) (T : ℝ) (hT : 1 < T)
    (hsupp : tsupport (sourceKPExteriorCoreLift K hζ f) ⊆
      {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    (InfinitePlace.nrComplexPlaces K : ℝ) *
        (∫ y, ‖f.val y‖^2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) ≤
      ∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
  let μ := sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)
  let μH := sourceKPHighCuspMeasure K hζ T
  let ν := sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
  let u := sourceKPExteriorCoreLift K hζ f
  let E := sourceKPExteriorCoreEnergyLift K hζ f
  let r : ℝ := InfinitePlace.nrComplexPlaces K
  let M := ∫ x, ‖u x‖^2 ∂μ
  let D := sourceKPExteriorCoreNormDerivative K hζ f 0 T hT
  have hPres := sourceKPHighCuspMeasure_val_preserving K hζ T
  have hEmb : MeasurableEmbedding
      (Subtype.val : SourceKPHighCuspAutomorphic K hζ T → SourceKPAutomorphicLevel K hζ) :=
    MeasurableEmbedding.subtype_coe (sourceKPHighCuspAutomorphic_isOpen K hζ T).measurableSet
  have hEpos (x) : 0 ≤ E x := sourceKPCompactCoreEnergy_nonneg K hζ f _
  have hEint : Integrable E μ := sourceKPExteriorCoreEnergyLift_integrable K hζ f
  have hMint : Integrable (fun x => ‖u x‖^2) μ := sourceKPExteriorCoreLift_normSq_integrable K hζ f
  have hMH : Integrable (fun q : SourceKPHighCuspAutomorphic K hζ T => ‖u q.val‖^2) μH :=
    hPres.integrable_comp_of_integrable hMint.restrict
  have hEH : Integrable (fun q : SourceKPHighCuspAutomorphic K hζ T => E q.val) μH :=
    hPres.integrable_comp_of_integrable hEint.restrict
  have hMass : (∫ q : SourceKPHighCuspAutomorphic K hζ T, ‖u q.val‖^2 ∂μH) = M := by
    rw [hPres.integral_comp hEmb (fun x => ‖u x‖^2)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : u x = 0 := by
      by_contra hn
      exact hx (hsupp (subset_tsupport _ hn))
    simp [hz]
  have hEnergy : (∫ q : SourceKPHighCuspAutomorphic K hζ T, E q.val ∂μH) ≤ ∫ x, E x ∂μ := by
    rw [hPres.integral_comp hEmb E]
    exact integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall hEpos) hEint
  obtain ⟨hDint,hIBP⟩ := sourceKPExteriorCoreNormDerivative_integral K hζ f T hT hsupp
  have hInt : (∫ q, D q ∂μH) ≤
      ∫ q : SourceKPHighCuspAutomorphic K hζ T, r * ‖u q.val‖^2 + E q.val ∂μH :=
    integral_mono hDint ((hMH.const_mul r).add hEH)
      (sourceKPExteriorCoreNormDerivative_zero_le_energy K hζ f T hT)
  rw [integral_add (hMH.const_mul r) hEH, integral_const_mul, hMass] at hInt
  have hEq : (∫ q, D q ∂μH) = (2*r)*M := hIBP
  rw [hEq] at hInt
  have hFull : r*M ≤ ∫ x, E x ∂μ := by nlinarith [hInt,hEnergy]
  have hπ := sourceKPAutomorphicCompactMk_measurePreserving K hζ (sourceKPArchHaar K hζ)
  have hMν : M = ∫ y, ‖f.val y‖^2 ∂ν := by
    change (∫ x, ‖f.val (sourceKPAutomorphicCompactMk K hζ x)‖^2 ∂μ) = _
    rw [show ν = Measure.map (sourceKPAutomorphicCompactMk K hζ) μ from hπ.map_eq.symm]
    exact (integral_map hπ.measurable.aemeasurable (f.property.1.norm.pow 2).aestronglyMeasurable).symm
  have hEν : (∫ x, E x ∂μ) = ∫ y, sourceKPCompactCoreEnergy K hζ f y ∂ν := by
    change (∫ x, sourceKPCompactCoreEnergy K hζ f (sourceKPAutomorphicCompactMk K hζ x) ∂μ) = _
    rw [show ν = Measure.map (sourceKPAutomorphicCompactMk K hζ) μ from hπ.map_eq.symm]
    exact (integral_map hπ.measurable.aemeasurable
      (sourceKPCompactCoreEnergy_continuous K hζ f).aestronglyMeasurable).symm
  rw [hMν,hEν] at hFull
  exact hFull

theorem sourceKPExteriorCore_one_sixth_coercive (f : sourceKPCompactC2Core K hζ)
    (T : ℝ) (hT : 1 < T)
    (hsupp : tsupport (sourceKPExteriorCoreLift K hζ f) ⊆
      {x | T < sourceKPAutomorphicOrbitHeight K hζ x}) :
    ((InfinitePlace.nrComplexPlaces K : ℝ) / 9) *
        (∫ y, ‖f.val y‖^2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) ≤
      (∫ y, sourceKPCompactCoreEnergy K hζ f y
        ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) -
        ((InfinitePlace.nrComplexPlaces K : ℝ) * (1 - 4 * (1 / 6 : ℝ)^2)) *
          (∫ y, ‖f.val y‖^2 ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  have h := sourceKPExteriorCore_hardy K hζ f T hT hsupp
  nlinarith

end
end ArtinMatthews
