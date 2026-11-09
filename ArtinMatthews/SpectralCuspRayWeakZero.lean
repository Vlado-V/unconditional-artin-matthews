module

public import ArtinMatthews.SpectralCuspRayLocal
public import ArtinMatthews.SpectralCuspRayTestPrimitive


set_option backward.privateInPublic true
@[expose] public section

/-! Weak derivative zero on the cusp tail implies actual almost
everywhere constancy, also for complex-valued locally integrable functions.
The proof uses genuine compact primitives of zero-mean scalar tests. -/
namespace ArtinMatthews.SpectralCuspRayRegularity
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
variable {Y : ℝ}

theorem ray_weak_zero_ae_const (hY : 0 ≤ Y) {f : ℝ → ℂ}
    (hf : LocallyIntegrableOn f (Ioi Y) volume)
    (hw : ∀ (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → HasCompactSupport ρ →
      tsupport ρ ⊆ Ioi Y → (∫ x, deriv ρ x • f x) = 0) :
    ∃ z : ℂ, f =ᵐ[volume.restrict (Ioi Y)] fun _ => z := by
  let b : ContDiffBump (Y+1) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let η : ℝ → ℝ := b.normed volume
  have hη : ContDiff ℝ ∞ η := b.contDiff_normed
  have hηc : HasCompactSupport η := b.hasCompactSupport_normed
  have hηs : tsupport η ⊆ Ioi Y := by
    intro x hx
    change x ∈ tsupport (b.normed volume) at hx
    rw [b.tsupport_normed_eq] at hx
    have H : |x - (Y+1)| ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, Real.dist_eq, b] using hx
    have h := (abs_le.mp H).1
    change Y < x
    linarith
  have hη1 : (∫ x, η x) = 1 := b.integral_normed
  have hηi : Integrable η volume := hη.continuous.integrable_of_hasCompactSupport hηc
  have hηf := integrable_ray_test_smul hf hη.continuous hηc hηs
  let z : ℂ := ∫ x, η x • f x
  have htest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ Ioi Y) : (∫ x, ψ x • (f x - z)) = 0 := by
    let r : ℝ := ∫ x, ψ x
    let σ : ℝ → ℝ := fun x => ψ x - r * η x
    have hσ : ContDiff ℝ ∞ σ := hψ.sub (contDiff_const.mul hη)
    have hσc : HasCompactSupport σ := hψc.sub (hηc.mul_left (f := fun _ => r))
    have hσs : tsupport σ ⊆ Ioi Y :=
      (tsupport_sub _ _).trans (union_subset hψs (tsupport_mul_subset_right.trans hηs))
    have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
    have hmean : (∫ x, σ x) = 0 := by
      dsimp only [σ]
      rw [integral_sub hψi (hηi.const_mul r), integral_const_mul, hη1, mul_one, sub_self]
    obtain ⟨ρ, hρ, hρc, hρs, hderiv⟩ :=
      rayTestPrimitive_exists hY σ hσ hσc hσs hmean
    have H := hw ρ hρ hρc hρs
    rw [hderiv] at H
    have hψf := integrable_ray_test_smul hf hψ.continuous hψc hψs
    change (∫ x, (ψ x - r * η x) • f x) = 0 at H
    simp_rw [sub_smul, mul_smul] at H
    have hrηf : Integrable (fun x => r • (η x • f x)) volume := hηf.smul r
    rw [integral_sub hψf hrηf, integral_smul] at H
    have hψz : Integrable (fun x => ψ x • z) volume := hψi.smul_const z
    simp_rw [smul_sub]
    rw [integral_sub hψf hψz, integral_smul_const]
    exact H
  have hlocal : LocallyIntegrableOn (fun x => f x - z) (Ioi Y) volume :=
    hf.sub (locallyIntegrableOn_const z)
  have hz := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocal htest
  refine ⟨z, ?_⟩
  filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioi] with x hx hxS
  exact sub_eq_zero.mp (hx hxS)

end
end ArtinMatthews.SpectralCuspRayRegularity
