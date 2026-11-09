module

public import ArtinMatthews.SpectralCompactSpectralCutoff
public import ArtinMatthews.SpectralGamma0CuspEigenfunctions


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite spectral windows for the constructed cuspidal energy eigenbasis.
The bound is qualitative; no uniform spectral counting estimate is assumed. -/
namespace ArtinMatthews
open Set
open scoped InnerProductSpace
noncomputable section

local instance gamma0Cutoff_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeightSpectralValue_norm (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : ‖i.1‖ = i.1.re := by
  calc
    _ = ‖(i.1.re : ℂ)‖ := congrArg norm (gamma0AllHeightSpectralValue_real N i).symm
    _ = _ := by simp [Real.norm_of_nonneg (gamma0AllHeightSpectralValue_pos N i).le]

theorem gamma0AllHeightGradientSpectralCutoff_finite (N : ℕ) [NeZero N] (R : ℝ) :
    {i : Gamma0AllHeightSpectralIndex N | gamma0AllHeightGradientSpectralValue N i ≤ R}.Finite := by
  have hR : 0 < max R 0 + 1 := by have := le_max_right R 0; linarith
  have hf := SpectralCompact.orthonormal_eigenvalue_cutoff_finite
    (gamma0AllHeightCoreGreen N) (gamma0AllHeightCoreGreen_compact N)
    (gamma0AllHeightSpectralBasis N) (gamma0AllHeightSpectralBasis N).orthonormal
    (fun i => i.1) (gamma0AllHeightSpectralBasis_eigen N) (inv_pos.mpr hR)
  apply hf.subset
  intro i hi
  change (max R 0 + 1)⁻¹ ≤ ‖i.1‖
  rw [gamma0AllHeightSpectralValue_norm]
  have hp := gamma0AllHeightSpectralValue_pos N i
  have hinv : i.1.re⁻¹ ≤ max R 0 + 1 := by
    change i.1.re⁻¹ - 1 ≤ R at hi
    have := le_max_left R 0
    linarith
  exact inv_le_of_inv_le₀ hp hinv

/-- A concrete finite index set retaining all eigenspace multiplicities. -/
def gamma0AllHeightGradientSpectralCutoff (N : ℕ) [NeZero N] (R : ℝ) :
    Finset (Gamma0AllHeightSpectralIndex N) :=
  (gamma0AllHeightGradientSpectralCutoff_finite N R).toFinset

theorem mem_gamma0AllHeightGradientSpectralCutoff (N : ℕ) [NeZero N] (R : ℝ)
    (i : Gamma0AllHeightSpectralIndex N) :
    i ∈ gamma0AllHeightGradientSpectralCutoff N R ↔ gamma0AllHeightGradientSpectralValue N i ≤ R := by
  exact (gamma0AllHeightGradientSpectralCutoff_finite N R).mem_toFinset

end
end ArtinMatthews
