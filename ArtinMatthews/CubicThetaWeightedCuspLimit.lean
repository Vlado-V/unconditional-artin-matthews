module

public import ArtinMatthews.CubicThetaCuspZeroUniform


set_option backward.privateInPublic true
@[expose] public section

/-! The full normalized zero-cusp limit for every finite periodic weight. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators Topology
open Complex UpperHalfPlane Filter

/-- A periodic holomorphic Eisenstein lattice theta function. -/
def weightedEisensteinTheta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    (τ : ℍ) : ℂ :=
  eisensteinWeightedGaussian w (eisensteinGaussianParameter τ)

/-- Actual weighted Poisson inversion, normalized for weight one. -/
theorem weightedEisensteinTheta_fricke_normalized {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (τ : ℍ) :
    weightedEisensteinTheta w (eisensteinPeriodFricke N τ) / (τ : ℂ) =
      (-3 * Complex.I / (Real.sqrt 3 : ℂ)) * eisensteinDualTheta w τ := by
  have ha : eisensteinGaussianParameter τ ≠ 0 := by
    intro h
    have hr := eisensteinGaussianParameter_re τ
    simp [h] at hr
  have hinv : 4 / (3 * (4 / (3 * eisensteinGaussianParameter τ))) =
      eisensteinGaussianParameter τ := by field_simp
  have h := eisensteinWeightedGaussian_inversion w
    (eisensteinGaussianParameter_re (eisensteinPeriodFricke N τ))
  rw [eisensteinPeriodFricke_parameter, hinv] at h
  change weightedEisensteinTheta w (eisensteinPeriodFricke N τ) =
    (2 / ((Real.sqrt 3 : ℂ) * (4 / (3 * eisensteinGaussianParameter τ)))) *
      eisensteinDualTheta w τ at h
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)).ne'
  rw [h]
  unfold eisensteinGaussianParameter
  field_simp [τ.ne_zero, hs]
  ring

/-- The cusp constant is the actual finite sum of the periodic weights. -/
theorem tendsto_weightedEisensteinTheta_fricke {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) :
    Tendsto (fun τ : ℍ => weightedEisensteinTheta w (eisensteinPeriodFricke N τ) /
      (τ : ℂ)) atImInfty
        (𝓝 ((-3 * Complex.I / (Real.sqrt 3 : ℂ)) * ∑ r, w r)) := by
  have h := (tendsto_eisensteinDualTheta w).const_mul
    (-3 * Complex.I / (Real.sqrt 3 : ℂ))
  simpa only [weightedEisensteinTheta_fricke_normalized] using h

/-- Vanishing follows from proved finite cancellation, uniformly in the real part. -/
theorem tendsto_weightedEisensteinTheta_fricke_zero {N : ℕ} [NeZero N]
    (w : Fin N × Fin N → ℂ) (hw : ∑ r, w r = 0) :
    Tendsto (fun τ : ℍ => weightedEisensteinTheta w (eisensteinPeriodFricke N τ) /
      (τ : ℂ)) atImInfty (𝓝 0) := by
  simpa only [hw, mul_zero] using tendsto_weightedEisensteinTheta_fricke w

end ArtinMatthews
