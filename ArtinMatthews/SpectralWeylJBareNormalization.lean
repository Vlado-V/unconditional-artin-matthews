module

public import ArtinMatthews.SpectralWeylKLNormalization
public import ArtinMatthews.SpectralWeylGaussianLimit


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory Filter Complex
open scoped Topology
noncomputable section

theorem spectralWeylJ_bare_density_normalization (H : ℂ → ℂ)
    (hEven : ∀ z : ℂ, H (-z) = H z) {X t : ℝ} (hX : 0 < X) (ht : 0 < t) :
    (spectralKLPlancherelWeight t : ℂ)*spectralWeylJMultiplier t X*H (t : ℂ) =
      (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
        (spectralWeylBareOrderIntegrand (fun ν x => Complex.besselJ ν x) H X (t : ℂ)+
          spectralWeylBareOrderIntegrand (fun ν x => Complex.besselJ ν x) H X ((-t : ℝ) : ℂ)) := by
  let M := (spectralKLPlancherelWeight t : ℂ)*spectralWeylJMultiplier t X*H (t : ℂ)
  let c : ℂ := -(4*I)/((Real.pi : ℂ)*(X : ℂ))
  let J := fun (ν : ℂ) (x : ℝ) => Complex.besselJ ν (x : ℂ)
  have hLeft : Tendsto (fun R : ℝ => M*Complex.exp (-2*((t : ℂ)/(R : ℂ))^2)) atTop (𝓝 M) := by
    simpa only [mul_one] using (spectralWeylGaussian_tendsto_one (t : ℂ)).const_mul M
  have hRight := ((spectralWeylContourIntegrand_tendsto J H X (t : ℂ)).add
    (spectralWeylContourIntegrand_tendsto J H X ((-t : ℝ) : ℂ))).const_mul c
  exact tendsto_nhds_unique hLeft (hRight.congr' (Eventually.of_forall fun R =>
    (spectralWeylJ_density_normalization H hEven R hX ht).symm))

theorem spectralWeylJBare_eq_orderIntegral (H : ℂ → ℂ)
    (hEven : ∀ z : ℂ, H (-z) = H z) {X : ℝ} (hX : 0 < X)
    (hF : Integrable (fun t : ℝ => spectralWeylBareOrderIntegrand
      (fun ν x => Complex.besselJ ν x) H X (t : ℂ))) :
    Integrable (fun t : ℝ => spectralWeylJMultiplier t X*H (t : ℂ)) spectralKLSpectralMeasure ∧
    (∫ t : ℝ, spectralWeylJMultiplier t X*H (t : ℂ) ∂spectralKLSpectralMeasure) =
      (-(4*I)/((Real.pi : ℂ)*(X : ℂ)))*
        (∫ t : ℝ, spectralWeylBareOrderIntegrand (fun ν x => Complex.besselJ ν x) H X (t : ℂ)) := by
  let F : ℝ → ℂ := fun t => spectralWeylBareOrderIntegrand (fun ν x => Complex.besselJ ν x) H X (t : ℂ)
  let c : ℂ := -(4*I)/((Real.pi : ℂ)*(X : ℂ))
  have hp : ∀ t : ℝ, 0 < t → 0 ≤ spectralKLPlancherelWeight t :=
    fun _ ht => (spectralKLPlancherelWeight_pos ht).le
  have hpoint (t : ℝ) (ht : 0 < t) :
      (spectralKLPlancherelWeight t : ℂ)*(spectralWeylJMultiplier t X*H (t : ℂ)) = c*(F t+F (-t)) := by
    simpa only [mul_assoc] using spectralWeylJ_bare_density_normalization H hEven hX ht
  have hsum := (hF.add hF.comp_neg).const_mul c
  have hi : IntegrableOn (fun t : ℝ => (spectralKLPlancherelWeight t : ℂ)*
      (spectralWeylJMultiplier t X*H (t : ℂ))) (Ioi (0 : ℝ)) := by
    apply hsum.integrableOn.congr_fun _ measurableSet_Ioi
    intro t ht
    exact (hpoint t ht).symm
  constructor
  · exact (spectralKLPositiveWeightMeasure_complex_integrable_iff _ _
      spectralKLPlancherelWeight_continuous.measurable hp).mpr hi
  · rw [spectralKLSpectralMeasure,spectralKLPositiveWeightMeasure_complex_integral _ _
      spectralKLPlancherelWeight_continuous.measurable hp]
    calc
      _ = ∫ t in Ioi (0 : ℝ), c*(F t+F (-t)) := setIntegral_congr_fun measurableSet_Ioi hpoint
      _ = c*(∫ t in Ioi (0 : ℝ), F t+F (-t)) := by rw [integral_const_mul]
      _ = _ := by rw [← spectralWeyl_full_line_half_sum F hF]

end
end ArtinMatthews
