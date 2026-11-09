module

public import ArtinMatthews.SpectralGamma0CuspEigenbasis
public import ArtinMatthews.SpectralGamma0CuspFormFaithful
public import ArtinMatthews.SpectralGamma0CuspMassSpace
public import ArtinMatthews.SpectralCompactCountable


set_option backward.privateInPublic true
@[expose] public section

/-! The constructed basis consists of genuine all-height mean-zero mass
vectors, has countable index, and lifts to the actual completed energy
domain with a nonnegative gradient spectral value. Completeness is still
asserted precisely in the closed energy mass image. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace MatrixGroups
namespace ArtinMatthews

local instance cuspEigenfunctions_energyInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspEigenfunctions_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

instance gamma0AllHeightSpectralIndex_countable (N : ℕ) [NeZero N] :
    Countable (Gamma0AllHeightSpectralIndex N) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp ℂ 2 (volume.restrict ModularGroup.fd)) := inferInstance
  let : SecondCountableTopology (Gamma0RegionL2 N) := inferInstance
  let : SecondCountableTopology (gamma0AllHeightEnergyMassSpace N) := inferInstance
  let : TopologicalSpace.SeparableSpace (gamma0AllHeightEnergyMassSpace N) := inferInstance
  exact SpectralCompact.orthonormal_countable (gamma0AllHeightSpectralBasis N).orthonormal

theorem gamma0AllHeightSpectralBasis_mem_cuspidal (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0AllHeightSpectralBasis N i).val ∈ gamma0AllHeightCuspidalMassSpace N :=
  gamma0AllHeight_energy_mass_closure_le_cuspidal N (gamma0AllHeightSpectralBasis N i).property

theorem gamma0AllHeightSpectralBasis_mean_zero (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2,ℤ)) (Y : ℝ) (hY : 0 < Y) :
    cuspHyperbolicAverageProjection (N : ℝ) Y hY
      (gamma0CuspMassRestriction N r Y hY (gamma0AllHeightSpectralBasis N i).val) = 0 :=
  (mem_gamma0AllHeightCuspidalMassSpace_iff N _).mp
    (gamma0AllHeightSpectralBasis_mem_cuspidal N i) r Y hY

def gamma0AllHeightSpectralEnergy (N : ℕ) [NeZero N] (i : Gamma0AllHeightSpectralIndex N) :
    gamma0AllHeightMeanZeroEnergy N :=
  gamma0AllHeightCoreWeakSolution N (i.1⁻¹ • gamma0AllHeightSpectralBasis N i)

theorem gamma0AllHeightSpectralEnergy_mass (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0AllHeightCoreInclusion N (gamma0AllHeightSpectralEnergy N i) =
      gamma0AllHeightSpectralBasis N i :=
  (gamma0AllHeightMassEnergyOperator_graph N _ _).mp
    (gamma0AllHeightSpectralBasis_operator_graph N i)

def gamma0AllHeightGradientSpectralValue (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : ℝ := i.1.re⁻¹-1

theorem gamma0AllHeightSpectralEnergy_weak (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0AllHeightMeanZeroEnergy N) :
    inner ℂ (gamma0AllHeightSpectralEnergy N i) v =
      (i.1.re⁻¹ : ℂ) * inner ℂ (gamma0AllHeightSpectralBasis N i)
        (gamma0AllHeightCoreInclusion N v) := by
  change inner ℂ (gamma0AllHeightCoreWeakSolution N _) v = _
  rw [gamma0AllHeightCoreWeakSolution_equation]
  rw [inner_smul_left (gamma0AllHeightSpectralBasis N i) (gamma0AllHeightCoreInclusion N v) i.1⁻¹]
  rw [← gamma0AllHeightSpectralValue_real N i]
  simp

theorem gamma0AllHeightSpectralEnergy_gradient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0AllHeightMeanZeroEnergy N) :
    inner ℂ (gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val)
      (gamma0EnergyGradient N v.val) =
        (gamma0AllHeightGradientSpectralValue N i : ℂ) *
          inner ℂ (gamma0AllHeightSpectralBasis N i) (gamma0AllHeightCoreInclusion N v) := by
  have he := gamma0AllHeightSpectralEnergy_weak N i v
  rw [gamma0AllHeightEnergy_inner,gamma0AllHeightSpectralEnergy_mass] at he
  unfold gamma0AllHeightGradientSpectralValue
  push_cast
  linear_combination he

theorem gamma0AllHeightGradientSpectralValue_nonneg (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) : 0 ≤ gamma0AllHeightGradientSpectralValue N i := by
  have he := gamma0AllHeightSpectralEnergy_gradient N i (gamma0AllHeightSpectralEnergy N i)
  rw [gamma0AllHeightSpectralEnergy_mass,
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ) (gamma0AllHeightSpectralBasis N i),
    (gamma0AllHeightSpectralBasis N).orthonormal.norm_eq_one i] at he
  norm_num at he
  have hr : ‖gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val‖^2 =
      gamma0AllHeightGradientSpectralValue N i := by exact_mod_cast he
  exact hr ▸ sq_nonneg _

end ArtinMatthews
