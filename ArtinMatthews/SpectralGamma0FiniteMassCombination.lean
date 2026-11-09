module

public import ArtinMatthews.SpectralGamma0EigenPlaneBound


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite real combinations of the normalized complex cuspidal basis. -/
noncomputable section
open Set MeasureTheory
open scoped MatrixGroups InnerProductSpace
namespace ArtinMatthews

theorem gamma0FullCuspidalSpectralBasis_ambient_orthonormal (N : ℕ) [NeZero N] :
    Orthonormal ℂ (fun i => (gamma0FullCuspidalSpectralBasis N i).val) := by
  have h := (gamma0AllHeightSpectralBasis N).orthonormal.comp_linearIsometry
    (gamma0AllHeightEnergyMassSpace N).subtypeₗᵢ
  change Orthonormal ℂ (fun i => (gamma0AllHeightSpectralBasis N i).val) at h
  simpa only [gamma0FullCuspidalSpectralBasis_coe] using h

def gamma0FiniteMassCombination (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    Gamma0RegionL2 N := ∑ i ∈ s, (c i : ℂ) • (gamma0FullCuspidalSpectralBasis N i).val

theorem gamma0FiniteMassCombination_eq_real_sum (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    gamma0FiniteMassCombination N s c = ∑ i ∈ s, c i • (gamma0FullCuspidalSpectralBasis N i).val := by
  exact Finset.sum_congr rfl (fun i _ => IsScalarTower.algebraMap_smul ℂ (c i) _)

theorem gamma0FiniteMassCombination_norm_sq (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    ‖gamma0FiniteMassCombination N s c‖^2 = ∑ i ∈ s, (c i)^2 := by
  have hi := (gamma0FullCuspidalSpectralBasis_ambient_orthonormal N).inner_sum
    (fun i => (c i : ℂ)) (fun i => (c i : ℂ)) s
  change inner ℂ (gamma0FiniteMassCombination N s c) (gamma0FiniteMassCombination N s c) = _ at hi
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gamma0FiniteMassCombination N s c)] at hi
  have hr := congrArg Complex.re hi
  simpa [pow_two] using hr

theorem gamma0Green_finiteMassCombination (N : ℕ) [NeZero N]
    (s : Finset (Gamma0AllHeightSpectralIndex N)) (c : Gamma0AllHeightSpectralIndex N → ℝ) :
    gamma0Green N (gamma0FiniteMassCombination N s c) =
      gamma0FiniteMassCombination N s (fun i => i.1.re*c i) := by
  simp only [gamma0FiniteMassCombination,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [gamma0FullCuspidalSpectralBasis_eigen,← gamma0AllHeightSpectralValue_real N i,smul_smul]
  congr 1
  push_cast
  simp only [Complex.ofReal_re]
  ring

end ArtinMatthews
