module

public import ArtinMatthews.SourceHyperbolicLocalGreen


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceHyperbolicGreen
open OAI.CubicEisenstein MeasureTheory Filter
open scoped Topology ContDiff BigOperators ENNReal
noncomputable section

theorem density_integrable {G : EuclideanSpatial → ℂ}
    (hG : Integrable (fun p => G p / (p 2 : ℂ)^3) volume) :
    Integrable G hyperbolicEuclideanVolume := by
  rw [hyperbolicEuclideanVolume]
  apply (integrable_withDensity_iff_integrable_smul' hyperbolicDensity_measurable
    (Eventually.of_forall (fun p => by simp only [hyperbolicDensity, ENNReal.ofReal_lt_top]))).2
  apply (hG.mono_measure Measure.restrict_le_self).congr
  filter_upwards [ae_restrict_mem euclideanUpperHalf_measurable] with p hp
  have hy : 0 < p 2 := hp
  rw [hyperbolicDensity, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, div_eq_mul_inv, mul_comm]

theorem density_integral_restrict (G : EuclideanSpatial → ℂ) :
    (∫ p, G p ∂hyperbolicEuclideanVolume) =
      ∫ p in euclideanUpperHalf, G p / (p 2 : ℂ)^3 := by
  have hμ : hyperbolicEuclideanVolume.restrict euclideanUpperHalf = hyperbolicEuclideanVolume := by
    rw [hyperbolicEuclideanVolume, restrict_withDensity euclideanUpperHalf_measurable,
      Measure.restrict_restrict euclideanUpperHalf_measurable, Set.inter_self]
  calc
    _ = ∫ p in euclideanUpperHalf, G p ∂hyperbolicEuclideanVolume := by rw [hμ]
    _ = _ := hyperbolicEuclidean_setIntegral_complex euclideanUpperHalf
      euclideanUpperHalf_measurable (Set.Subset.refl _) G

theorem density_integral (G : EuclideanSpatial → ℂ)
    (hG : ∀ p ∉ euclideanUpperHalf, G p=0) :
    (∫ p, G p ∂hyperbolicEuclideanVolume) = ∫ p, G p / (p 2 : ℂ)^3 := by
  rw [density_integral_restrict]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [hG p hp, zero_div]

def gradientPair (φ f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) : ℂ :=
  (p 2 : ℂ)^2 * ∑ j : Fin 3, star (coordinatePartial φ j p) * coordinatePartial f j p

theorem gradientPair_div_cube (φ f : EuclideanSpatial → ℂ) (p : EuclideanSpatial) :
    gradientPair φ f p / (p 2 : ℂ)^3 = pairDensity φ f p := by
  rw [gradientPair, pairDensity, ← Finset.sum_div]
  by_cases hp : p 2=0
  · simp [hp]
  · field_simp [Complex.ofReal_ne_zero.mpr hp]

theorem gradientPair_zero_outside {φ : EuclideanSpatial → ℂ}
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) (f : EuclideanSpatial → ℂ)
    (p : EuclideanSpatial) (hp : p ∉ euclideanUpperHalf) : gradientPair φ f p=0 := by
  have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
  have hz (j : Fin 3) : coordinatePartial φ j p=0 := by
    rw [coordinatePartial, fderiv_of_notMem_tsupport ℝ hn]
    rfl
  simp only [gradientPair, hz, star_zero, zero_mul, Finset.sum_const_zero, mul_zero]

theorem gradientPair_integrable {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    Integrable (gradientPair φ f) hyperbolicEuclideanVolume := by
  apply density_integrable
  simpa only [gradientPair_div_cube] using pairDensity_integrable hf hφ hc hsupp

theorem tested_laplacian_integrable_hyperbolic {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    Integrable (fun p => star (φ p) * positiveEuclideanLaplacian f p) hyperbolicEuclideanVolume :=
  density_integrable (tested_laplacian_integrable hf hφ hc hsupp)

theorem green_hyperbolic {f φ : EuclideanSpatial → ℂ}
    (hf : ∀ p ∈ euclideanUpperHalf, ContDiffAt ℝ 2 f p)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, gradientPair φ f p ∂hyperbolicEuclideanVolume) =
      ∫ p, star (φ p) * positiveEuclideanLaplacian f p ∂hyperbolicEuclideanVolume := by
  rw [density_integral _ (gradientPair_zero_outside hsupp f)]
  rw [density_integral _ (fun p hp => by
    have hz : φ p=0 := image_eq_zero_of_notMem_tsupport (fun h => hp (hsupp h))
    rw [hz, star_zero, zero_mul])]
  simp_rw [gradientPair_div_cube]
  exact local_green hf hφ hc hsupp

theorem green_hyperbolic_of_contDiffOn {f φ : EuclideanSpatial → ℂ}
    (hf : ContDiffOn ℝ 2 f euclideanUpperHalf)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, gradientPair φ f p ∂hyperbolicEuclideanVolume) =
      ∫ p, star (φ p) * positiveEuclideanLaplacian f p ∂hyperbolicEuclideanVolume := by
  apply green_hyperbolic _ hφ hc hsupp
  intro p hp
  exact (hf p hp).contDiffAt (upperHalf_isOpen.mem_nhds hp)

theorem test_contDiff_of_contDiffOn {φ : EuclideanSpatial → ℂ}
    (hφ : ContDiffOn ℝ 2 φ euclideanUpperHalf)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) : ContDiff ℝ 2 φ := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ euclideanUpperHalf
  · exact (hφ p hp).contDiffAt (upperHalf_isOpen.mem_nhds hp)
  · have hn : p ∉ tsupport φ := fun h => hp (hsupp h)
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : EuclideanSpatial => (0 : ℂ)) p).congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp hn)

theorem green_hyperbolic_on {f φ : EuclideanSpatial → ℂ}
    (hf : ContDiffOn ℝ 2 f euclideanUpperHalf)
    (hφ : ContDiffOn ℝ 2 φ euclideanUpperHalf) (hc : HasCompactSupport φ)
    (hsupp : tsupport φ ⊆ euclideanUpperHalf) :
    (∫ p, gradientPair φ f p ∂hyperbolicEuclideanVolume) =
      ∫ p, star (φ p) * positiveEuclideanLaplacian f p ∂hyperbolicEuclideanVolume :=
  green_hyperbolic_of_contDiffOn hf (test_contDiff_of_contDiffOn hφ hsupp) hc hsupp

end
end ArtinMatthews.SourceHyperbolicGreen
