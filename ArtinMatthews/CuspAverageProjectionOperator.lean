module

public import ArtinMatthews.CuspAverageProjectionBase
public import Mathlib.Analysis.InnerProductSpace.Adjoint


set_option backward.privateInPublic true
@[expose] public section

/-! A concrete orthogonal projection onto the vertically varying functions
in the actual unnormalized strip L² space. Its horizontal-integral formula
is established separately. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set
open scoped ENNReal InnerProduct

@[simp] theorem cuspHorizontalMeasure_univ (w : ℝ) :
    cuspHorizontalMeasure w univ = ENNReal.ofReal w := by
  simp [cuspHorizontalMeasure, Real.volume_Ioc]

instance cuspHorizontalMeasure_isFinite (w : ℝ) : IsFiniteMeasure (cuspHorizontalMeasure w) :=
  ⟨by rw [cuspHorizontalMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

instance cuspVerticalMeasure_sigmaFinite (Y : ℝ) : SigmaFinite (cuspVerticalMeasure Y) := by
  dsimp [cuspVerticalMeasure]
  infer_instance

abbrev CuspStripL2 (w Y : ℝ) := Lp ℂ 2 (cuspStripMeasure w Y)

/-- The vertical norm carries the full horizontal mass; it is not silently
normalized to a probability measure. -/
abbrev CuspVerticalL2 (w Y : ℝ) :=
  Lp ℂ 2 ((cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y)

/-- Pulling a function back along the vertical coordinate is an exact
isometry with the stated horizontal-mass factor. -/
def cuspVerticalPullback (w Y : ℝ) : CuspVerticalL2 w Y →ₗᵢ[ℂ] CuspStripL2 w Y :=
  Lp.compMeasurePreservingₗᵢ ℂ Prod.snd
    ⟨measurable_snd, by exact Measure.map_snd_prod⟩

/-- The actual bounded projection is pullback composed with its Hilbert
adjoint, using an isometry rather than an assumed averaging bound. -/
def cuspAverageProjection (w Y : ℝ) : CuspStripL2 w Y →L[ℂ] CuspStripL2 w Y :=
  (cuspVerticalPullback w Y).toContinuousLinearMap ∘L
    (cuspVerticalPullback w Y).toContinuousLinearMap.adjoint

theorem cuspAverageProjection_norm_le (w Y : ℝ) : ‖cuspAverageProjection w Y‖ ≤ 1 := by
  let U := (cuspVerticalPullback w Y).toContinuousLinearMap
  have hu : ‖U‖ ≤ 1 := (cuspVerticalPullback w Y).norm_toContinuousLinearMap_le
  have hua : ‖U.adjoint‖ ≤ 1 := by simpa only [ContinuousLinearMap.adjoint.norm_map] using hu
  change ‖U ∘L U.adjoint‖ ≤ 1
  calc
    _ ≤ ‖U‖ * ‖U.adjoint‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul hu hua (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem cuspAverageProjection_norm_apply_le (w Y : ℝ) (f : CuspStripL2 w Y) :
    ‖cuspAverageProjection w Y f‖ ≤ ‖f‖ := by
  exact ((cuspAverageProjection w Y).le_opNorm f).trans
    (mul_le_of_le_one_left (norm_nonneg _) (cuspAverageProjection_norm_le w Y))

theorem cuspAverageProjection_idempotent (w Y : ℝ) (f : CuspStripL2 w Y) :
    cuspAverageProjection w Y (cuspAverageProjection w Y f) = cuspAverageProjection w Y f := by
  let U := (cuspVerticalPullback w Y).toContinuousLinearMap
  have h := congrArg (fun T => T (U.adjoint f)) (cuspVerticalPullback w Y).adjoint_comp_self
  change U.adjoint (U (U.adjoint f)) = U.adjoint f at h
  change U (U.adjoint (U (U.adjoint f))) = U (U.adjoint f)
  exact congrArg U h

theorem cuspAverageProjection_adjoint (w Y : ℝ) :
    (cuspAverageProjection w Y).adjoint = cuspAverageProjection w Y := by
  simp only [cuspAverageProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]

theorem cuspAverageProjection_inner (w Y : ℝ) (f g : CuspStripL2 w Y) :
    inner ℂ (cuspAverageProjection w Y f) g = inner ℂ f (cuspAverageProjection w Y g) := by
  simpa only [cuspAverageProjection_adjoint] using
    ((cuspAverageProjection w Y).adjoint_inner_right f g).symm

/-- The mean-zero subspace is a genuine closed linear subspace. Its
horizontal-integral characterization will identify this kernel explicitly. -/
def cuspMeanZeroL2 (w Y : ℝ) : Submodule ℂ (CuspStripL2 w Y) :=
  (cuspAverageProjection w Y).ker

theorem cuspMeanZeroL2_isClosed (w Y : ℝ) :
    IsClosed (cuspMeanZeroL2 w Y : Set (CuspStripL2 w Y)) :=
  (cuspAverageProjection w Y).isClosed_ker

theorem cuspMeanZeroL2_sub_average (w Y : ℝ) (f : CuspStripL2 w Y) :
    f - cuspAverageProjection w Y f ∈ cuspMeanZeroL2 w Y := by
  change cuspAverageProjection w Y (f - cuspAverageProjection w Y f) = 0
  rw [map_sub, cuspAverageProjection_idempotent, sub_self]

end ArtinMatthews
