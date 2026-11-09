module

public import ArtinMatthews.SpectralGamma0LocalizationBound
public import ArtinMatthews.SpectralCompactDenseCore


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact localization on the completed Γ₀ energy space. -/

noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)

private theorem energy_test_linear_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EnergyTestLinear N ψ = gamma0EnergyTest N ψ := rfl

private theorem localized_seed_linear_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0LocalizedSeedLinear φ ha hab hφ N ψ = gamma0LocalizedSeedLp φ ha hab hφ N ψ := rfl

private theorem localized_bound (N : ℕ) [NeZero N] :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0LocalizedSeedLinear φ ha hab hφ N ψ‖ ≤ C * ‖gamma0EnergyTestLinear N ψ‖ := by
  obtain ⟨C,_,hC⟩ := gamma0LocalizedSeedLp_bound φ ha hab hφ
  refine ⟨C,fun ψ => ?_⟩
  rw [energy_test_linear_apply,localized_seed_linear_apply]
  exact hC N ψ

private theorem localization_extension_exists (N : ℕ) [NeZero N] :
    ∃ A : gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume : Measure UpperHalfPlane),
      ∀ ψ, A (gamma0EnergyTestLinear N ψ) = gamma0LocalizedSeedLinear φ ha hab hφ N ψ :=
  exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0LocalizedSeedLinear φ ha hab hφ N) (gamma0EnergyTestLinear N)
    (gamma0EnergyTest_dense N)
    (gamma0LocalizedSeedLinear φ ha hab hφ N).map_add
    (gamma0LocalizedSeedLinear φ ha hab hφ N).map_smul
    (gamma0EnergyTestLinear N).map_add (gamma0EnergyTestLinear N).map_smul
    (localized_bound φ ha hab hφ N)

/-- The bounded extension of literal compact localization from the actual
smooth core to its actual energy completion. -/
def gamma0EnergyLocalization (N : ℕ) [NeZero N] :
    gamma0EnergySpace N →L[ℂ] Lp ℂ 2 (volume : Measure UpperHalfPlane) :=
  (localization_extension_exists φ ha hab hφ N).choose

theorem gamma0EnergyLocalization_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EnergyLocalization φ ha hab hφ N (gamma0EnergyTest N ψ) =
      gamma0LocalizedSeedLp φ ha hab hφ N ψ := by
  have h := (localization_extension_exists φ ha hab hφ N).choose_spec ψ
  rw [energy_test_linear_apply,localized_seed_linear_apply] at h
  exact h

/-- Fixed compact localization is a genuinely compact operator on the
completed global energy space; compactness is proved by local Rellich. -/
theorem gamma0EnergyLocalization_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0EnergyLocalization φ ha hab hφ N) := by
  apply compactOperator_of_dense_core (gamma0EnergyTestLinear N)
    (gamma0EnergyTest_dense N)
  change IsCompact (closure (range (fun ψ :
    {ψ : h2SmoothCompactSeeds // ‖gamma0EnergyTestLinear N ψ‖ ≤ 2} =>
    gamma0EnergyLocalization φ ha hab hφ N (gamma0EnergyTest N ψ.val))))
  simp_rw [gamma0EnergyLocalization_apply]
  apply gamma0LocalizedSeedLp_rellich φ ha hab hφ N
    (fun ψ : {ψ : h2SmoothCompactSeeds // ‖gamma0EnergyTestLinear N ψ‖ ≤ 2} => ψ.val)
    (by norm_num : (0 : ℝ) ≤ 4)
  intro ψ
  have h : ‖gamma0EnergyTest N ψ.val‖ ≤ 2 := ψ.property
  have hh := (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mpr h
  norm_num only [sq] at hh ⊢
  exact hh

end ArtinMatthews
