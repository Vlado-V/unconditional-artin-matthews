module

public import ArtinMatthews.SpectralGaussianCosine
public import ArtinMatthews.SpectralWeylRadiusSubstitution


set_option backward.privateInPublic true
@[expose] public section

/-! Actual Gaussian evaluation of the supported radial cosine kernel.
This removes the square-root boundary singularity with its full Jacobian. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace ArtinMatthews

def spectralWeylRadialKernel (A b X : ℝ) : ℝ :=
  if Real.sqrt A < X then
    2*Real.cos (b*Real.sqrt (X^2-A))/Real.sqrt (X^2-A) else 0

def spectralWeylRadialGaussian (A b p X : ℝ) : ℝ :=
  Real.exp (-p*X^2)*X*spectralWeylRadialKernel A b X

theorem spectralWeylRadialGaussian_support (A b p : ℝ) :
    Function.support (spectralWeylRadialGaussian A b p) ⊆ Ioi (Real.sqrt A) := by
  intro X hX
  by_contra h
  change ¬Real.sqrt A < X at h
  exact hX (by simp [spectralWeylRadialGaussian,spectralWeylRadialKernel,h])

theorem spectralWeylRadialGaussian_substitution {A : ℝ} (hA : 0 < A) (b p : ℝ)
    {u : ℝ} (hu : 0 < u) :
    (u/spectralWeylRadius A u)*spectralWeylRadialGaussian A b p (spectralWeylRadius A u) =
      (2*Real.exp (-p*A))*(Real.exp (-p*u^2)*Real.cos (b*u)) := by
  have hR : Real.sqrt A < spectralWeylRadius A u := by
    have hmem : spectralWeylRadius A u ∈ spectralWeylRadius A '' Ioi (0 : ℝ) := ⟨u,hu,rfl⟩
    rwa [spectralWeylRadius_image hA] at hmem
  have hs : Real.sqrt ((spectralWeylRadius A u)^2-A) = u := by
    rw [spectralWeylRadius_sq hA,add_sub_cancel_left,Real.sqrt_sq hu.le]
  unfold spectralWeylRadialGaussian spectralWeylRadialKernel
  rw [ite_eq_left hR,hs,spectralWeylRadius_sq hA]
  rw [show -p*(A+u^2) = -p*A+-p*u^2 by ring,Real.exp_add]
  field_simp [(spectralWeylRadius_pos hA u).ne',hu.ne']

theorem spectralWeylRadialGaussian_integrable {A p : ℝ} (hA : 0 < A) (hp : 0 < p) (b : ℝ) :
    Integrable (spectralWeylRadialGaussian A b p) := by
  apply (integrableOn_iff_integrable_of_support_subset (spectralWeylRadialGaussian_support A b p)).mp
  apply (spectralWeylRadius_integrable hA _).mpr
  apply ((spectralGaussianCosine_integrable hp b).const_mul (2*Real.exp (-p*A))).restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (spectralWeylRadialGaussian_substitution hA b p hu).symm

theorem spectralWeylRadialGaussian_integral {A p : ℝ} (hA : 0 < A) (hp : 0 < p) (b : ℝ) :
    (∫ X in Ioi (0 : ℝ), spectralWeylRadialGaussian A b p X) =
      Real.sqrt (Real.pi/p)*Real.exp (-p*A-b^2/(4*p)) := by
  have hzero (X : ℝ) (hX : X ∉ Ioi (Real.sqrt A)) :
      spectralWeylRadialGaussian A b p X = 0 := by
    change ¬Real.sqrt A < X at hX
    simp [spectralWeylRadialGaussian,spectralWeylRadialKernel,hX]
  have hzero0 (X : ℝ) (hX : X ∉ Ioi (0 : ℝ)) :
      spectralWeylRadialGaussian A b p X = 0 := by
    apply hzero
    intro h
    exact hX ((Real.sqrt_nonneg A).trans_lt h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero0,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,spectralWeylRadius_integral hA]
  calc
    _ = (2*Real.exp (-p*A))*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      exact spectralWeylRadialGaussian_substitution hA b p hu
    _ = Real.exp (-p*A)*((2 : ℝ)*(∫ u in Ioi (0 : ℝ), Real.exp (-p*u^2)*Real.cos (b*u))) := by ring
    _ = _ := by
      rw [spectralGaussianCosine_Ioi hp b,show -p*A-b^2/(4*p) = -p*A+(-(b^2)/(4*p)) by ring,Real.exp_add]
      ring

end ArtinMatthews
