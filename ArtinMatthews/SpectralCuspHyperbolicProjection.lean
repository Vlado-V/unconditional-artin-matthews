module

public import ArtinMatthews.CuspAverageHyperbolicTransport


set_option backward.privateInPublic true
@[expose] public section

/-! The actual bounded orthogonal cusp-average projection in the
invariant hyperbolic strip L2 space. -/

namespace ArtinMatthews
noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProduct

abbrev CuspHyperbolicL2 (w Y : ℝ) :=
  Lp ℂ 2 (volume.restrict (hyperbolicCuspStrip w Y))

def cuspHyperbolicAverageProjection (w Y : ℝ) (hY : 0 < Y) :
    CuspHyperbolicL2 w Y →L[ℂ] CuspHyperbolicL2 w Y :=
  (cuspHyperbolicPullback w Y hY).toContinuousLinearMap ∘L
    cuspAverageProjection w Y ∘L (cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint

theorem cuspHyperbolicPullback_adjoint_self (w Y : ℝ) (hY : 0 < Y)
    (f : CuspStripL2 w Y) :
    (cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint
      (cuspHyperbolicPullback w Y hY f) = f := by
  exact congrArg (fun T => T f) (cuspHyperbolicPullback w Y hY).adjoint_comp_self

theorem cuspHyperbolicAverageProjection_pullback (w Y : ℝ) (hY : 0 < Y)
    (f : CuspStripL2 w Y) :
    cuspHyperbolicAverageProjection w Y hY (cuspHyperbolicPullback w Y hY f) =
      cuspHyperbolicPullback w Y hY (cuspAverageProjection w Y f) := by
  change cuspHyperbolicPullback w Y hY (cuspAverageProjection w Y
    ((cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint
      (cuspHyperbolicPullback w Y hY f))) = _
  rw [cuspHyperbolicPullback_adjoint_self]

theorem cuspHyperbolicAverageProjection_norm_apply_le (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) : ‖cuspHyperbolicAverageProjection w Y hY f‖ ≤ ‖f‖ := by
  let U := (cuspHyperbolicPullback w Y hY).toContinuousLinearMap
  have hu : ‖U‖ ≤ 1 := (cuspHyperbolicPullback w Y hY).norm_toContinuousLinearMap_le
  have hua : ‖U.adjoint‖ ≤ 1 := by simpa only [ContinuousLinearMap.adjoint.norm_map] using hu
  change ‖cuspHyperbolicPullback w Y hY (cuspAverageProjection w Y (U.adjoint f))‖ ≤ ‖f‖
  rw [(cuspHyperbolicPullback w Y hY).norm_map]
  exact (cuspAverageProjection_norm_apply_le w Y _).trans
    ((U.adjoint.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _) hua))

theorem cuspHyperbolicAverageProjection_norm_le (w Y : ℝ) (hY : 0 < Y) :
    ‖cuspHyperbolicAverageProjection w Y hY‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul] using cuspHyperbolicAverageProjection_norm_apply_le w Y hY f

theorem cuspHyperbolicAverageProjection_idempotent (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) :
    cuspHyperbolicAverageProjection w Y hY (cuspHyperbolicAverageProjection w Y hY f) =
      cuspHyperbolicAverageProjection w Y hY f := by
  change cuspHyperbolicPullback w Y hY (cuspAverageProjection w Y
      ((cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint
        (cuspHyperbolicPullback w Y hY (cuspAverageProjection w Y
          ((cuspHyperbolicPullback w Y hY).toContinuousLinearMap.adjoint f))))) = _
  rw [cuspHyperbolicPullback_adjoint_self, cuspAverageProjection_idempotent]
  rfl

theorem cuspHyperbolicAverageProjection_adjoint (w Y : ℝ) (hY : 0 < Y) :
    (cuspHyperbolicAverageProjection w Y hY).adjoint = cuspHyperbolicAverageProjection w Y hY := by
  simp only [cuspHyperbolicAverageProjection, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, cuspAverageProjection_adjoint, ContinuousLinearMap.comp_assoc]

theorem cuspHyperbolicAverageProjection_inner (w Y : ℝ) (hY : 0 < Y)
    (f g : CuspHyperbolicL2 w Y) :
    inner ℂ (cuspHyperbolicAverageProjection w Y hY f) g =
      inner ℂ f (cuspHyperbolicAverageProjection w Y hY g) := by
  simpa only [cuspHyperbolicAverageProjection_adjoint] using
    ((cuspHyperbolicAverageProjection w Y hY).adjoint_inner_right f g).symm

def cuspHyperbolicMeanZeroL2 (w Y : ℝ) (hY : 0 < Y) : Submodule ℂ (CuspHyperbolicL2 w Y) :=
  (cuspHyperbolicAverageProjection w Y hY).ker

theorem cuspHyperbolicMeanZeroL2_isClosed (w Y : ℝ) (hY : 0 < Y) :
    IsClosed (cuspHyperbolicMeanZeroL2 w Y hY : Set (CuspHyperbolicL2 w Y)) :=
  (cuspHyperbolicAverageProjection w Y hY).isClosed_ker

theorem cuspHyperbolicMeanZeroL2_sub_average (w Y : ℝ) (hY : 0 < Y)
    (f : CuspHyperbolicL2 w Y) :
    f-cuspHyperbolicAverageProjection w Y hY f ∈ cuspHyperbolicMeanZeroL2 w Y hY := by
  change cuspHyperbolicAverageProjection w Y hY (f-cuspHyperbolicAverageProjection w Y hY f) = 0
  rw [map_sub, cuspHyperbolicAverageProjection_idempotent, sub_self]

end
end ArtinMatthews
