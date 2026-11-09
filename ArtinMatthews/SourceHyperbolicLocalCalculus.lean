module

public import OAI.NumberTheory.DirichletL.MeanSquare.UnitRows
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section

theorem upperHalf_isOpen : IsOpen euclideanUpperHalf :=
  isOpen_lt continuous_const (by fun_prop)

def coordinatePartial (f : EuclideanSpatial → ℂ) (j : Fin 3) (p : EuclideanSpatial) : ℂ :=
  fderiv ℝ f p (euclideanCoordinateVector j)

def weightedPartial (f : EuclideanSpatial → ℂ) (j : Fin 3) (p : EuclideanSpatial) : ℂ :=
  coordinatePartial f j p / (p 2 : ℂ)

theorem coordinatePartial_contDiffAt {f : EuclideanSpatial → ℂ} {p : EuclideanSpatial}
    (hf : ContDiffAt ℝ 2 f p) (j : Fin 3) : ContDiffAt ℝ 1 (coordinatePartial f j) p := by
  exact (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

theorem weightedPartial_contDiffAt {f : EuclideanSpatial → ℂ} {p : EuclideanSpatial}
    (hf : ContDiffAt ℝ 2 f p) (hp : 0 < p 2) (j : Fin 3) :
    ContDiffAt ℝ 1 (weightedPartial f j) p := by
  have hh : ContDiffAt ℝ 1 (fun q : EuclideanSpatial => (q 2 : ℂ)) p :=
    euclideanHeightCLM.contDiff.contDiffAt
  simpa only [weightedPartial, div_eq_mul_inv] using!
    (coordinatePartial_contDiffAt hf j).mul (hh.fun_inv (Complex.ofReal_ne_zero.mpr hp.ne'))

theorem weightedPartial_derivative_continuousAt {f : EuclideanSpatial → ℂ} {p : EuclideanSpatial}
    (hf : ContDiffAt ℝ 2 f p) (hp : 0 < p 2) (j k : Fin 3) :
    ContinuousAt (coordinatePartial (weightedPartial f j) k) p := by
  exact (((weightedPartial_contDiffAt hf hp j).fderiv_right (m := 0) (by norm_num)).clm_apply
    contDiffAt_const).continuousAt

theorem compact_mul_integrable {φ F : EuclideanSpatial → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hF : ∀ p ∈ tsupport φ, ContinuousAt F p) :
    Integrable (fun p => φ p * F p) volume := by
  have hprod : Continuous (fun p => φ p * F p) := by
    apply continuous_of_tsupport
    intro p hp
    exact hφ.continuousAt.mul (hF p (tsupport_mul_subset_left hp))
  exact hprod.integrable_of_hasCompactSupport hc.mul_right

theorem compact_star_mul_integrable {φ F : EuclideanSpatial → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hF : ∀ p ∈ tsupport φ, ContinuousAt F p) :
    Integrable (fun p => star (φ p) * F p) volume := by
  have hs : tsupport (fun p => star (φ p)) = tsupport φ := by
    unfold tsupport
    congr 1
    ext p
    simp only [Function.mem_support, star_ne_zero]
  apply compact_mul_integrable hφ.star
  · change IsCompact (tsupport (fun p => star (φ p)))
    rwa [hs]
  · intro p hp
    exact hF p (hs ▸ hp)

theorem test_partial_compact {φ : EuclideanSpatial → ℂ} (hc : HasCompactSupport φ) (j : Fin 3) :
    HasCompactSupport (coordinatePartial φ j) :=
  hc.fderiv_apply ℝ (euclideanCoordinateVector j)

theorem test_partial_support {φ : EuclideanSpatial → ℂ} (j : Fin 3) :
    tsupport (coordinatePartial φ j) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ (euclideanCoordinateVector j)

theorem test_partial_continuous {φ : EuclideanSpatial → ℂ} (hφ : ContDiff ℝ 2 φ) (j : Fin 3) :
    Continuous (coordinatePartial φ j) := by
  exact ((hφ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous

theorem weightedPartial_derivative {f : EuclideanSpatial → ℂ} {p : EuclideanSpatial}
    (hf : ContDiffAt ℝ 2 f p) (hp : 0 < p 2) (j k : Fin 3) :
    coordinatePartial (weightedPartial f j) k p =
      (coordinatePartial (coordinatePartial f j) k p * (p 2 : ℂ) -
        coordinatePartial f j p * (euclideanCoordinateVector k 2 : ℂ)) / (p 2 : ℂ)^2 := by
  have hpart := ((coordinatePartial_contDiffAt hf j).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (euclideanCoordinateVector k)
  have hheight := (euclideanHeightCLM.hasFDerivAt (x := p)).hasLineDerivAt (euclideanCoordinateVector k)
  change HasDerivAt (fun t : ℝ => coordinatePartial f j (p+t • euclideanCoordinateVector k))
    (coordinatePartial (coordinatePartial f j) k p) 0 at hpart
  change HasDerivAt (fun t : ℝ => ((p+t • euclideanCoordinateVector k) 2 : ℂ))
    (euclideanCoordinateVector k 2 : ℂ) 0 at hheight
  have hn : ((p+(0 : ℝ) • euclideanCoordinateVector k) 2 : ℂ) ≠ 0 := by
    simpa only [zero_smul, add_zero] using (Complex.ofReal_ne_zero.mpr hp.ne')
  have hquot := hpart.div hheight hn
  have hline : HasLineDerivAt ℝ (weightedPartial f j)
      ((coordinatePartial (coordinatePartial f j) k p * (p 2 : ℂ) -
        coordinatePartial f j p * (euclideanCoordinateVector k 2 : ℂ)) / (p 2 : ℂ)^2)
      p (euclideanCoordinateVector k) := by
    simpa only [HasLineDerivAt, weightedPartial, Pi.div_apply, zero_smul, add_zero] using! hquot
  exact (((weightedPartial_contDiffAt hf hp j).differentiableAt (by norm_num)).hasFDerivAt.hasLineDerivAt
    (euclideanCoordinateVector k)).unique hline

end
end ArtinMatthews.SourceHyperbolicGreen
