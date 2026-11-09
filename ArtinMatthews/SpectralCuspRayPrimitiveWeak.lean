module

public import ArtinMatthews.SpectralCuspRayLocal
public import ArtinMatthews.SpectralCuspRayTestPrimitive


set_option backward.privateInPublic true
@[expose] public section

/-! Actual primitive weak identities on the cusp tail. The real
integration-by-parts argument is the tail-interval form of the extracted
SobolevProjection primitive proof; complex values are handled by real CLMs. -/
namespace ArtinMatthews.SpectralCuspRayRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {Y : ℝ}

theorem ray_primitive_weak_derivative {g : ℝ → ℝ}
    (hg : LocallyIntegrableOn g (Ioi Y) volume)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ x, (∫ t in (Y+1)..x, g t) * deriv ρ x) = -(∫ x, g x * ρ x) := by
  obtain ⟨a, b, ha, ha1, hb1, hs⟩ := rayTest_support_enclosure ρ hρc hρs
  have hab : a ≤ b := by linarith
  have hzero : ρ a = 0 ∧ ρ b = 0 := by
    constructor <;> apply image_eq_zero_of_notMem_tsupport <;>
      intro h <;> have := hs h <;> simp_all
  let F := fun x => ∫ t in (Y+1)..x, g t
  have hgi := ray_interval_integrable hg ha (by linarith : Y<b)
  have h1 : Y+1 ∈ uIcc a b := by
    rw [uIcc_of_le hab]
    exact ⟨ha1.le, hb1.le⟩
  have hF : AbsolutelyContinuousOnInterval F a b :=
    hgi.absolutelyContinuousOnInterval_intervalIntegral h1
  have hρa : AbsolutelyContinuousOnInterval ρ a b :=
    (hρ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hfd : ∀ᵐ x, x ∈ uIcc a b → deriv F x = g x := by
    filter_upwards [hgi.ae_hasDerivAt_integral] with x hx hmem
    exact (hx hmem (Y+1) h1).deriv
  have he := hF.integral_mul_deriv_eq_deriv_mul hρa
  rw [hzero.1, hzero.2, mul_zero, mul_zero, sub_self, zero_sub] at he
  have hi : (∫ x in a..b, deriv F x * ρ x) = ∫ x in a..b, g x * ρ x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hfd] with x hx hmem
    rw [hx (uIoc_subset_uIcc hmem)]
  rw [hi] at he
  have hleft : Function.support (fun x => F x * deriv ρ x) ⊆ Ioc a b := by
    intro x hx
    have hd : x ∈ tsupport (deriv ρ) :=
      subset_tsupport _ (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)
    exact Ioo_subset_Ioc_self (hs (tsupport_deriv_subset hd))
  have hright : Function.support (fun x => g x * ρ x) ⊆ Ioc a b := by
    intro x hx
    exact Ioo_subset_Ioc_self (hs (subset_tsupport _
      (Function.mem_support.mpr (mul_ne_zero_iff.mp hx).2)))
  rwa [intervalIntegral.integral_eq_integral_of_support_subset hleft,
    intervalIntegral.integral_eq_integral_of_support_subset hright] at he

theorem ray_primitive_weak_derivative_complex {g : ℝ → ℂ}
    (hg : LocallyIntegrableOn g (Ioi Y) volume)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) :
    (∫ x, deriv ρ x • (∫ t in (Y+1)..x, g t)) = -(∫ x, ρ x • g x) := by
  have hds : tsupport (deriv ρ) ⊆ Ioi Y := tsupport_deriv_subset.trans hρs
  have hleft := integrable_ray_test_smul
    ((ray_primitive_continuousOn hg).locallyIntegrableOn measurableSet_Ioi)
    (hρ.continuous_deriv (by simp)) hρc.deriv hds
  have hright := integrable_ray_test_smul hg hρ.continuous hρc hρs
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ x, deriv ρ x • (∫ t in (Y+1)..x, g t)) = -L (∫ x, ρ x • g x) := by
    have hr := ray_primitive_weak_derivative (L.locallyIntegrableOn_comp hg) ρ hρ hρc hρs
    rw [← L.integral_comp_comm hleft, ← L.integral_comp_comm hright]
    have he : (∫ x, L (deriv ρ x • (∫ t in (Y+1)..x, g t))) =
        ∫ x, (∫ t in (Y+1)..x, L (g t)) * deriv ρ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change L (deriv ρ x • (∫ t in (Y+1)..x, g t)) =
          (∫ t in (Y+1)..x, L (g t)) * deriv ρ x
        by_cases hx : Y < x
        · rw [map_smul, ← L.intervalIntegral_comp_comm
            (ray_interval_integrable hg (by linarith : Y<Y+1) hx)]
          exact mul_comm _ _
        · have hd : deriv ρ x = 0 := image_eq_zero_of_notMem_tsupport
            (fun h => hx (hds h))
          simp only [hd, zero_smul, map_zero, mul_zero]
    rw [he]
    simpa only [Function.comp_apply, map_smul, smul_eq_mul, mul_comm] using hr
  apply Complex.ext
  · simpa only [Complex.reCLM_apply, Complex.neg_re] using hL Complex.reCLM
  · simpa only [Complex.imCLM_apply, Complex.neg_im] using hL Complex.imCLM

end
end ArtinMatthews.SpectralCuspRayRegularity
