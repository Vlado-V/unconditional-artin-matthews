module

public import ArtinMatthews.SourceKPAdelicCutoffParameterJoint
public import ArtinMatthews.SourceKPCompactCutoffContinuity
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import ArtinMatthews.CompactSupportL2Derivative


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compactly restricted cutoff is entire with values in Haar L². -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory Filter
open scoped NumberField AdeleRing MatrixGroups Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "L" => Lp ℂ 2 μ

def sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative (T : ℝ)
    (s : ℂ) (x : Y) : ℂ :=
  deriv (fun z => sourceKPAutomorphicCompactCutoffEisenstein K hζ T z x) s

theorem sourceKPAutomorphicCompactCutoffEisenstein_hasDerivAt {T : ℝ}
    (hT : 0 < T) (s : ℂ) (x : Y) :
    HasDerivAt (fun z => sourceKPAutomorphicCompactCutoffEisenstein K hζ T z x)
      (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T s x) s :=
  (sourceKPAutomorphicCompactCutoffEisenstein_entire K hζ hT x s).hasDerivAt

theorem sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative_adelic
    (T : ℝ) (s : ℂ) (q : SourceKPAdelicProjective K hζ) :
    sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T s
      (sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ q)) =
        sourceKPAdelicCutoffEisensteinParameterDerivative K hζ T s q :=
  rfl

theorem sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative_joint_continuous
    {T : ℝ} (hT : 0 < T) :
    Continuous (fun p : ℂ × Y =>
      sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T p.1 p.2) := by
  apply sourceKPAutomorphicCompactFamily_continuous_of_matrices K hζ
  intro qf
  exact sourceKPAdelicCutoffEisensteinParameterDerivative_joint_matrix_continuous K hζ hT qf

private theorem continuous_parameter_slice {X : Type*} [TopologicalSpace X]
    (F : ℂ → X → ℂ) (hF : Continuous (fun p : ℂ × X => F p.1 p.2)) (s : ℂ) :
    Continuous (F s) := by
  have hs : Continuous (fun x : X => (s,x)) := continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using hF.comp hs

private def cutoffRestriction {T : ℝ} (hT : 0 < T) (S : Set Y) (s : ℂ) : C(S, ℂ) :=
  compactSupportRestriction S (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s)
    (continuous_parameter_slice (sourceKPAutomorphicCompactCutoffEisenstein K hζ T)
      (sourceKPAutomorphicCompactCutoffEisenstein_joint_continuous K hζ hT) s)

private def cutoffDerivativeRestriction {T : ℝ} (hT : 0 < T) (S : Set Y) (s : ℂ) : C(S, ℂ) :=
  compactSupportRestriction S (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T s)
    (continuous_parameter_slice (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T)
      (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative_joint_continuous K hζ hT) s)

private def cutoffRestrictionToHaarL2 (S : Set Y) (hS : IsCompact S) : C(S, ℂ) →L[ℂ] L := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : IsFiniteMeasureOnCompacts μ := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  exact compactContinuousToL2L S hS.measurableSet μ hS.measure_ne_top

private theorem cutoffRestrictionToHaarL2_coe (S : Set Y) (hS : IsCompact S)
    (f : Y → ℂ) (hf : Continuous f) :
    (cutoffRestrictionToHaarL2 K hζ S hS (compactSupportRestriction S f hf) : Y → ℂ) =ᵐ[μ]
      S.indicator f := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let : IsFiniteMeasureOnCompacts μ := sourceKPAutomorphicCompactHaar_finiteOnCompacts K hζ
  have h := compactContinuousToL2_coe S hS.measurableSet μ hS.measure_ne_top
    (compactSupportRestriction S f hf)
  filter_upwards [h] with x hx
  by_cases hmem : x ∈ S
  · rw [Set.indicator_of_mem hmem]
    exact hx.trans (compactContinuousZeroExtension_mem S _ x hmem)
  · rw [Set.indicator_of_notMem hmem]
    exact hx.trans (compactContinuousZeroExtension_notMem S _ x hmem)

def sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) : L :=
  cutoffRestrictionToHaarL2 K hζ S hS (cutoffRestriction K hζ hT S s)

def sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) : L :=
  cutoffRestrictionToHaarL2 K hζ S hS (cutoffDerivativeRestriction K hζ hT S s)

theorem sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_coe {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) :
    (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ hT S hS s : Y → ℂ) =ᵐ[μ]
      S.indicator (sourceKPAutomorphicCompactCutoffEisenstein K hζ T s) := by
  unfold sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 cutoffRestriction
  apply cutoffRestrictionToHaarL2_coe

theorem sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative_coe {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) :
    (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative K hζ hT S hS s : Y → ℂ) =ᵐ[μ]
      S.indicator (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T s) := by
  unfold sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative cutoffDerivativeRestriction
  apply cutoffRestrictionToHaarL2_coe

theorem sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_hasDerivAt {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) :
    HasDerivAt (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ hT S hS)
      (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative K hζ hT S hS s) s := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hG : Continuous (fun p : ℂ × S => cutoffDerivativeRestriction K hζ hT S p.1 p.2) := by
    change Continuous (fun p : ℂ × S =>
      sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T p.1 p.2.val)
    simpa only [Function.comp_def] using
      (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative_joint_continuous K hζ hT).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd) :
          Continuous (fun p : ℂ × S => (p.1,p.2.val)))
  have hderiv (z : ℂ) (x : S) :
      HasDerivAt (fun w => cutoffRestriction K hζ hT S w x)
        (cutoffDerivativeRestriction K hζ hT S z x) z := by
    change HasDerivAt (fun w => sourceKPAutomorphicCompactCutoffEisenstein K hζ T w x.val)
      (sourceKPAutomorphicCompactCutoffEisensteinParameterDerivative K hζ T z x.val) z
    exact sourceKPAutomorphicCompactCutoffEisenstein_hasDerivAt K hζ hT z x.val
  have h := hasDerivAt_continuousMap_of_jointlyContinuous
    (cutoffRestriction K hζ hT S) (cutoffDerivativeRestriction K hζ hT S) hG hderiv s
  unfold sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2
    sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2Derivative
  exact (cutoffRestrictionToHaarL2 K hζ S hS).hasFDerivAt.comp_hasDerivAt s h

theorem sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_entire {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) :
    Differentiable ℂ (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ hT S hS) :=
  fun s => (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_hasDerivAt K hζ hT S hS s).differentiableAt

theorem sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_analyticAt {T : ℝ}
    (hT : 0 < T) (S : Set Y) (hS : IsCompact S) (s : ℂ) :
    AnalyticAt ℂ (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2 K hζ hT S hS) s :=
  (sourceKPAutomorphicCompactCutoffEisensteinRestrictedL2_entire K hζ hT S hS).analyticAt s

end
end ArtinMatthews
