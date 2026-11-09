module

public import ArtinMatthews.SpectralGaussianMellin


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gaussian transform of the doubled-order K function.
Its defining integral and continuity are proved before any evaluation. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open OAI.CubicEisenstein

namespace ArtinMatthews

def spectralWeberKTransform (ν : ℂ) (p : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x

theorem spectralWeberK_base_integrable {ν : ℂ} (hν : |ν.re| < 1/2) :
    IntegrableOn (schlafliBesselK (2*ν)) (Ioi (0 : ℝ)) := by
  have hh : |(2*ν).re| < (1 : ℂ).re := by
    norm_num [Complex.mul_re,abs_mul]
    linarith
  simpa only [sub_self,Complex.cpow_zero,one_mul] using
    schlafliBesselK_mellin_integrable (2*ν) 1 hh

theorem spectralWeberK_gaussian_norm_le (ν : ℂ) {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    ‖Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x‖ ≤
      ‖schlafliBesselK (2*ν) x‖ := by
  rw [norm_mul,Complex.norm_exp]
  have heq : -(p : ℂ)*(x : ℂ)^2 = ((-p*x^2 : ℝ) : ℂ) := by push_cast; rfl
  have he : (-(p : ℂ)*(x : ℂ)^2).re = -p*x^2 := by rw [heq,Complex.ofReal_re]
  rw [he]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))

theorem spectralWeberK_integrable {ν : ℂ} (hν : |ν.re| < 1/2) {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x)
      (Ioi (0 : ℝ)) := by
  have hK : Integrable (schlafliBesselK (2*ν)) (volume.restrict (Ioi (0 : ℝ))) := spectralWeberK_base_integrable hν
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  apply hK.norm.mono' ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(p : ℂ)*(x : ℂ)^2))).aestronglyMeasurable.mul
    hK.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (spectralWeberK_gaussian_norm_le ν hp.le)

theorem spectralWeberK_continuousAt {ν : ℂ} (hν : |ν.re| < 1/2) {p : ℝ} (hp : 0 < p) :
    ContinuousAt (spectralWeberKTransform ν) p := by
  have hK := spectralWeberK_base_integrable hν
  apply continuousAt_of_dominated
    (F := fun q x : ℝ => Complex.exp (-(q : ℂ)*(x : ℂ)^2)*schlafliBesselK (2*ν) x)
    (bound := fun x : ℝ => ‖schlafliBesselK (2*ν) x‖)
  · exact Filter.Eventually.of_forall (fun q =>
      (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-(q : ℂ)*(x : ℂ)^2))).aestronglyMeasurable.mul
        hK.aestronglyMeasurable)
  · filter_upwards [isOpen_Ioi.mem_nhds hp] with q hq
    exact Filter.Eventually.of_forall (spectralWeberK_gaussian_norm_le ν hq.le)
  · exact hK.norm
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)

end ArtinMatthews
