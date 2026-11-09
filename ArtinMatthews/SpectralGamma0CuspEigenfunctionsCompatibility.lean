module

public import ArtinMatthews.SpectralGamma0CuspFormCompatibility


set_option backward.privateInPublic true
@[expose] public section

/-! Exact transfer of the constructed spectral data to the full cuspidal
mass kernel and to arbitrary ambient energy tests, conditional explicitly
on the separately proved analytic Green-invariance statement. -/
noncomputable section
namespace ArtinMatthews

local instance cuspEigenCompatibility_energyInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspEigenCompatibility_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

variable (N : ℕ) [NeZero N]
variable (hG : ∀ f ∈ gamma0AllHeightCuspidalMassSpace N,
  gamma0Green N f ∈ gamma0AllHeightCuspidalMassSpace N)

theorem gamma0AllHeightSpectralEnergy_mass_ambient (i : Gamma0AllHeightSpectralIndex N) :
    gamma0EnergyInclusion N (gamma0AllHeightSpectralEnergy N i).val =
      (gamma0AllHeightSpectralBasis N i).val :=
  congrArg Subtype.val (gamma0AllHeightSpectralEnergy_mass N i)

include hG

theorem gamma0AllHeightSpectralEnergy_eq_ambient_of_green_invariant
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0AllHeightSpectralEnergy N i).val =
      gamma0WeakSolution N (i.1⁻¹ • (gamma0AllHeightSpectralBasis N i).val) :=
  gamma0AllHeightWeakSolution_eq_ambient_of_green_invariant N hG
    (i.1⁻¹ • gamma0AllHeightSpectralBasis N i)

theorem gamma0AllHeightSpectralEnergy_ambient_weak_of_green_invariant
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0AllHeightSpectralEnergy N i).val v =
      (i.1.re⁻¹ : ℂ) * inner ℂ (gamma0AllHeightSpectralBasis N i).val
        (gamma0EnergyInclusion N v) := by
  rw [gamma0AllHeightSpectralEnergy_eq_ambient_of_green_invariant N hG,
    gamma0WeakSolution_equation,
    inner_smul_left (gamma0AllHeightSpectralBasis N i).val (gamma0EnergyInclusion N v) i.1⁻¹,
    ← gamma0AllHeightSpectralValue_real N i]
  simp

theorem gamma0AllHeightSpectralEnergy_ambient_gradient_of_green_invariant
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val)
      (gamma0EnergyGradient N v) =
        (gamma0AllHeightGradientSpectralValue N i : ℂ) *
          inner ℂ (gamma0AllHeightSpectralBasis N i).val (gamma0EnergyInclusion N v) := by
  have he := gamma0AllHeightSpectralEnergy_ambient_weak_of_green_invariant N hG i v
  rw [gamma0FormEnergy_inner,gamma0AllHeightSpectralEnergy_mass_ambient] at he
  unfold gamma0AllHeightGradientSpectralValue
  push_cast
  linear_combination he

def gamma0FullCuspidalSpectralBasisOfInvariant :
    HilbertBasis (Gamma0AllHeightSpectralIndex N) ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  HilbertBasis.ofRepr
    ((LinearIsometryEquiv.ofEq (gamma0AllHeightEnergyMassSpace N)
      (gamma0AllHeightCuspidalMassSpace N) (gamma0AllHeight_mass_closure_eq_of_green_invariant N hG)).symm.trans
        (gamma0AllHeightSpectralBasis N).repr)

theorem gamma0FullCuspidalSpectralBasisOfInvariant_coe
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasisOfInvariant N hG i).val =
      (gamma0AllHeightSpectralBasis N i).val := rfl

theorem gamma0FullCuspidalSpectralBasisOfInvariant_eigen
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0Green N (gamma0FullCuspidalSpectralBasisOfInvariant N hG i).val =
      i.1 • (gamma0FullCuspidalSpectralBasisOfInvariant N hG i).val := by
  rw [gamma0FullCuspidalSpectralBasisOfInvariant_coe,
    ← gamma0AllHeightGreen_eq_ambient_of_green_invariant N hG,
    gamma0AllHeightSpectralBasis_eigen]
  rfl

end ArtinMatthews
