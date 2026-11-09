module

public import ArtinMatthews.SourceHyperbolicCommonRadialDerivative
public import ArtinMatthews.SourceKPExteriorRadialSupport
public import ArtinMatthews.SourceKPCompactEnergyRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! The actual high-cusp radial derivative of a compact scalar core test. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Set SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPExteriorCoreLift (f : sourceKPCompactC2Core K hζ) :
    SourceKPAutomorphicLevel K hζ → ℂ :=
  f.val ∘ sourceKPAutomorphicCompactMk K hζ

theorem sourceKPExteriorCoreLift_continuous (f : sourceKPCompactC2Core K hζ) :
    Continuous (sourceKPExteriorCoreLift K hζ f) :=
  f.property.1.comp (sourceKPAutomorphicCompactMk_isOpenQuotientMap K hζ).continuous

theorem sourceKPExteriorCoreLift_hasCompactSupport (f : sourceKPCompactC2Core K hζ) :
    HasCompactSupport (sourceKPExteriorCoreLift K hζ f) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (sourceKPAutomorphicCompactMk_isCompact_preimage K hζ f.property.2.1)
  intro x hx
  exact subset_tsupport _ hx

theorem sourceKPExteriorCoreLift_normSq_integrable (f : sourceKPCompactC2Core K hζ) :
    Integrable (fun x => ‖sourceKPExteriorCoreLift K hζ f x‖^2)
      (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let : IsFiniteMeasureOnCompacts (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)) :=
    sourceKPAutomorphicMeasure_finiteOnCompacts K hζ _
  have hc : HasCompactSupport (fun x : SourceKPAutomorphicLevel K hζ =>
      ‖sourceKPExteriorCoreLift K hζ f x‖^2) := by
    apply HasCompactSupport.of_support_subset_isCompact (sourceKPExteriorCoreLift_hasCompactSupport K hζ f)
    intro x hx
    apply subset_tsupport (sourceKPExteriorCoreLift K hζ f)
    intro hz
    apply hx
    change ‖sourceKPExteriorCoreLift K hζ f x‖^2 = 0
    simp [hz]
  exact ((sourceKPExteriorCoreLift_continuous K hζ f).norm.pow 2).integrable_of_hasCompactSupport hc

def sourceKPExteriorCoreEnergyLift (f : sourceKPCompactC2Core K hζ) :
    SourceKPAutomorphicLevel K hζ → ℝ :=
  sourceKPCompactCoreEnergy K hζ f ∘ sourceKPAutomorphicCompactMk K hζ

theorem sourceKPExteriorCoreEnergyLift_integrable (f : sourceKPCompactC2Core K hζ) :
    Integrable (sourceKPExteriorCoreEnergyLift K hζ f)
      (sourceKPAutomorphicMeasure K hζ (sourceKPArchHaar K hζ)) :=
  (sourceKPAutomorphicCompactMk_measurePreserving K hζ _).integrable_comp_of_integrable
    (sourceKPCompactCoreEnergy_integrable K hζ f)

def sourceKPExteriorCoreValue (f : sourceKPCompactC2Core K hζ) (t T : ℝ) (hT : 1 < T)
    (q : SourceKPHighCuspAutomorphic K hζ T) : ℂ :=
  sourceKPExteriorCoreLift K hζ f (sourceKPHighCuspRadialValue K hζ t T hT q)

theorem sourceKPExteriorCoreValue_zero (f : sourceKPCompactC2Core K hζ) (T : ℝ) (hT : 1 < T)
    (q : SourceKPHighCuspAutomorphic K hζ T) :
    sourceKPExteriorCoreValue K hζ f 0 T hT q = sourceKPExteriorCoreLift K hζ f q.val := by
  rw [sourceKPExteriorCoreValue, sourceKPHighCuspRadialValue_zero]

theorem sourceKPExteriorCoreValue_measurable (f : sourceKPCompactC2Core K hζ) (t T : ℝ)
    (hT : 1 < T) : Measurable (sourceKPExteriorCoreValue K hζ f t T hT) :=
  (sourceKPExteriorCoreLift_continuous K hζ f).measurable.comp
    (sourceKPHighCuspRadialValue_measurable K hζ t T hT)

theorem sourceKPExteriorCoreValue_chart (f : sourceKPCompactC2Core K hζ) (t T : ℝ)
    (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPExteriorCoreValue K hζ f t T hT (sourceKPHighCuspProjection K hζ T x) =
      sourceKPCompactChartPullback K hζ f.val x.val.2
        (sourceKPArchRadialEuclideanCurve K (sourceKPArchGramCoordinates K hζ x.val.1) t) := by
  rw [sourceKPExteriorCoreValue, sourceKPHighCuspRadialValue_rep,
    sourceKPCompactChartPullback, ite_eq_left (sourceKPArchRadialEuclideanCurve_positive K _ _)]
  apply congrArg f.val
  change sourceKPAutomorphicCompactMk K hζ
      (sourceKPArchComponentPoint K hζ x.val.2 (sourceKPArchRadialFlow K hζ t x.val.1)) = _
  rw [← sourceKPUpperToCompact_mk]
  change sourceKPUpperToCompact K hζ x.val.2
      (sourceKPArchGramCoordinates K hζ (sourceKPArchRadialFlow K hζ t x.val.1)) =
    sourceKPUpperToCompact K hζ x.val.2
      (sourceKPArchEuclideanUpperMap K (sourceKPArchRadialEuclideanCurve K
        (sourceKPArchGramCoordinates K hζ x.val.1) t))
  rw [sourceKPArchRadialFlow_coordinates, sourceKPArchRadialEuclideanCurve,
    sourceKPArchUpperEuclideanMap_left_inverse]

def sourceKPExteriorCoreRadialDerivative (f : sourceKPCompactC2Core K hζ) (t T : ℝ)
    (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) : ℂ :=
  deriv (fun s => sourceKPExteriorCoreValue K hζ f s T hT q) t

theorem sourceKPExteriorCoreValue_chart_hasDerivAt (f : sourceKPCompactC2Core K hζ)
    (t T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T) :
    HasDerivAt (fun s => sourceKPExteriorCoreValue K hζ f s T hT (sourceKPHighCuspProjection K hζ T x))
      (productRadial (sourceKPCompactChartPullback K hζ f.val x.val.2)
        (sourceKPArchRadialEuclideanCurve K (sourceKPArchGramCoordinates K hζ x.val.1) t)) t := by
  have he := funext (fun s => sourceKPExteriorCoreValue_chart K hζ f s T hT x)
  rw [he]
  exact sourceKPArchRadialEuclideanTest_hasDerivAt K
    ((f.property.2.2 x.val.2).of_le (by norm_num)) _ t

theorem sourceKPExteriorCoreRadialDerivative_chart (f : sourceKPCompactC2Core K hζ)
    (t T : ℝ) (hT : 1 < T) (x : SourceKPHighCuspFinite K hζ T) :
    sourceKPExteriorCoreRadialDerivative K hζ f t T hT (sourceKPHighCuspProjection K hζ T x) =
      productRadial (sourceKPCompactChartPullback K hζ f.val x.val.2)
        (sourceKPArchRadialEuclideanCurve K (sourceKPArchGramCoordinates K hζ x.val.1) t) :=
  (sourceKPExteriorCoreValue_chart_hasDerivAt K hζ f t T hT x).deriv

theorem sourceKPExteriorCoreValue_hasDerivAt (f : sourceKPCompactC2Core K hζ)
    (t T : ℝ) (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    HasDerivAt (fun s => sourceKPExteriorCoreValue K hζ f s T hT q)
      (sourceKPExteriorCoreRadialDerivative K hζ f t T hT q) t := by
  obtain ⟨x,rfl⟩ := sourceKPHighCusp_representative K hζ T q
  rw [sourceKPExteriorCoreRadialDerivative_chart]
  exact sourceKPExteriorCoreValue_chart_hasDerivAt K hζ f t T hT x

theorem sourceKPExteriorCoreRadialDerivative_normSq_le (f : sourceKPCompactC2Core K hζ)
    (t T : ℝ) (hT : 1 < T) (q : SourceKPHighCuspAutomorphic K hζ T) :
    ‖sourceKPExteriorCoreRadialDerivative K hζ f t T hT q‖^2 ≤
      (InfinitePlace.nrComplexPlaces K : ℝ) *
        sourceKPExteriorCoreEnergyLift K hζ f (sourceKPHighCuspRadialValue K hζ t T hT q) := by
  obtain ⟨x,rfl⟩ := sourceKPHighCusp_representative K hζ T q
  let p := sourceKPArchGramCoordinates K hζ x.val.1
  have hE : sourceKPExteriorCoreEnergyLift K hζ f
      (sourceKPHighCuspRadialValue K hζ t T hT (sourceKPHighCuspProjection K hζ T x)) =
        productGradientEnergy (sourceKPCompactChartPullback K hζ f.val x.val.2)
          (sourceKPArchRadialEuclideanCurve K p t) := by
    rw [sourceKPHighCuspRadialValue_rep]
    change sourceKPCompactCoreEnergy K hζ f (sourceKPAutomorphicCompactMk K hζ
      (sourceKPArchComponentPoint K hζ x.val.2 (sourceKPArchRadialFlow K hζ t x.val.1))) = _
    rw [← sourceKPUpperToCompact_mk, sourceKPCompactCoreEnergy_chart]
    change productGradientEnergy (sourceKPCompactChartPullback K hζ f.val x.val.2)
      (sourceKPArchUpperEuclideanMap K (sourceKPArchGramCoordinates K hζ
        (sourceKPArchRadialFlow K hζ t x.val.1))) = _
    rw [sourceKPArchRadialFlow_coordinates]
    rfl
  rw [sourceKPExteriorCoreRadialDerivative_chart, hE, ← sourceKPRadialComplexCount K hζ]
  exact productRadial_norm_sq_le_gradient _ _

end
end ArtinMatthews
