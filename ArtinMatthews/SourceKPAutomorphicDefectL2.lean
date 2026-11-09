module

public import ArtinMatthews.SourceKPAutomorphicDefectContinuity
public import ArtinMatthews.SourceKPAutomorphicCompactHaar
public import ArtinMatthews.CompactSupportL2Derivative
public import Mathlib.Analysis.Complex.CauchyIntegral


set_option backward.privateInPublic true
@[expose] public section

/-! The literal compact defect is an entire family in the actual
automorphic L2 space with its prescribed Haar measure. -/

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem defectBand_measurable (T : ℝ) :
    MeasurableSet {x : SourceKPAutomorphicCompactLevel K hζ |
      sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T} :=
  ((lowerSemicontinuous_iff_isClosed_preimage.mp
    (sourceKPAutomorphicCompactOrbitHeight_lowerSemicontinuous K hζ)) (2*T)).measurableSet

private theorem defectBand_measure_ne_top (T : ℝ) :
    sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
      {x : SourceKPAutomorphicCompactLevel K hζ |
        sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T} ≠ ⊤ :=
  (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T)).measure_ne_top

private theorem compactDefect_continuous {T : ℝ} (hT : 0 < T) (s : ℂ) :
    Continuous (sourceKPAutomorphicCompactCutoffDefect K hζ hT s) := by
  have hm : Continuous (fun x : SourceKPAutomorphicCompactLevel K hζ => (s,x)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using
    (sourceKPAutomorphicCompactCutoffDefect_joint_continuous K hζ hT).comp hm

private theorem compactDefectDerivative_continuous {T : ℝ} (hT : 0 < T) (s : ℂ) :
    Continuous (sourceKPAutomorphicCompactDefectParameterDerivative K hζ hT s) := by
  have hm : Continuous (fun x : SourceKPAutomorphicCompactLevel K hζ => (s,x)) :=
    continuous_const.prodMk continuous_id
  simpa only [Function.comp_def] using
    (sourceKPAutomorphicCompactDefectParameterDerivative_joint_continuous K hζ hT).comp hm

theorem sourceKPAutomorphicCompactCutoffDefect_memLp {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    MemLp (sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s)
      2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let S := {x : SourceKPAutomorphicCompactLevel K hζ |
    sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T}
  have hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hfinite : sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) S ≠ ⊤ :=
    defectBand_measure_ne_top K hζ T
  exact compactSupport_memLp S (defectBand_measurable K hζ T)
    (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) hfinite
    (sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s)
    (compactDefect_continuous K hζ (lt_of_lt_of_le zero_lt_one hT) s)
    (sourceKPAutomorphicCompactCutoffDefect_support K hζ hT s)

theorem sourceKPAutomorphicCompactDefectParameterDerivative_memLp {T : ℝ}
    (hT : 1 ≤ T) (s : ℂ) :
    MemLp (sourceKPAutomorphicCompactDefectParameterDerivative K hζ
      (lt_of_lt_of_le zero_lt_one hT) s)
      2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)) := by
  let S := {x : SourceKPAutomorphicCompactLevel K hζ |
    sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T}
  have hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  exact compactSupport_memLp S (defectBand_measurable K hζ T)
    (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))
    (defectBand_measure_ne_top K hζ T)
    (sourceKPAutomorphicCompactDefectParameterDerivative K hζ (lt_of_lt_of_le zero_lt_one hT) s)
    (compactDefectDerivative_continuous K hζ (lt_of_lt_of_le zero_lt_one hT) s)
    (sourceKPAutomorphicCompactDefectParameterDerivative_support K hζ hT s)

def sourceKPAutomorphicDefectL2 {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ) :=
  (sourceKPAutomorphicCompactCutoffDefect_memLp K hζ hT s).toLp
    (sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s)

def sourceKPAutomorphicDefectDerivativeL2 {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    SourceKPAutomorphicL2 K hζ (sourceKPArchHaar K hζ) :=
  (sourceKPAutomorphicCompactDefectParameterDerivative_memLp K hζ hT s).toLp
    (sourceKPAutomorphicCompactDefectParameterDerivative K hζ
      (lt_of_lt_of_le zero_lt_one hT) s)

theorem sourceKPAutomorphicDefectL2_ae {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    sourceKPAutomorphicDefectL2 K hζ hT s =ᵐ[
      sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)]
        sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT) s :=
  (sourceKPAutomorphicCompactCutoffDefect_memLp K hζ hT s).coeFn_toLp

theorem sourceKPAutomorphicDefectDerivativeL2_ae {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    sourceKPAutomorphicDefectDerivativeL2 K hζ hT s =ᵐ[
      sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)]
        sourceKPAutomorphicCompactDefectParameterDerivative K hζ
          (lt_of_lt_of_le zero_lt_one hT) s :=
  (sourceKPAutomorphicCompactDefectParameterDerivative_memLp K hζ hT s).coeFn_toLp

theorem sourceKPAutomorphicDefectL2_hasDerivAt {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    HasDerivAt (sourceKPAutomorphicDefectL2 K hζ hT)
      (sourceKPAutomorphicDefectDerivativeL2 K hζ hT s) s := by
  let S := {x : SourceKPAutomorphicCompactLevel K hζ |
    sourceKPAutomorphicCompactOrbitHeight K hζ x ≤ 2*T}
  have hS : IsCompact S := sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ (2*T)
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  exact hasDerivAt_toLp_of_fixed_compact_support S (defectBand_measurable K hζ T)
    (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))
    (defectBand_measure_ne_top K hζ T)
    (sourceKPAutomorphicCompactCutoffDefect K hζ (lt_of_lt_of_le zero_lt_one hT))
    (sourceKPAutomorphicCompactDefectParameterDerivative K hζ (lt_of_lt_of_le zero_lt_one hT))
    (sourceKPAutomorphicCompactCutoffDefect_joint_continuous K hζ
      (lt_of_lt_of_le zero_lt_one hT))
    (sourceKPAutomorphicCompactDefectParameterDerivative_joint_continuous K hζ
      (lt_of_lt_of_le zero_lt_one hT))
    (sourceKPAutomorphicCompactCutoffDefect_support K hζ hT)
    (sourceKPAutomorphicCompactDefectParameterDerivative_support K hζ hT)
    (sourceKPAutomorphicCompactCutoffDefect_hasDerivAt K hζ
      (lt_of_lt_of_le zero_lt_one hT))
    (sourceKPAutomorphicCompactCutoffDefect_memLp K hζ hT)
    (sourceKPAutomorphicCompactDefectParameterDerivative_memLp K hζ hT) s

theorem sourceKPAutomorphicDefectL2_entire {T : ℝ} (hT : 1 ≤ T) :
    Differentiable ℂ (sourceKPAutomorphicDefectL2 K hζ hT) :=
  fun s => (sourceKPAutomorphicDefectL2_hasDerivAt K hζ hT s).differentiableAt

theorem sourceKPAutomorphicDefectL2_analyticAt {T : ℝ} (hT : 1 ≤ T) (s : ℂ) :
    AnalyticAt ℂ (sourceKPAutomorphicDefectL2 K hζ hT) s :=
  (sourceKPAutomorphicDefectL2_entire K hζ hT).analyticAt s

end
end ArtinMatthews
