module

public import ArtinMatthews.SpectralGamma0GreenCuspInvariant
public import ArtinMatthews.SpectralGamma0CuspEigenfunctionsCompatibility


set_option backward.privateInPublic true
@[expose] public section

/-! Unconditional spectral data on the genuine all-height cuspidal mass kernel.
The analytic Green-preservation theorem discharges the explicit hypothesis in
previous structural compatibility lemmas. Coordinate smoothness is a separate
elliptic regularity result. -/
namespace ArtinMatthews
open Set Topology
open scoped InnerProductSpace MatrixGroups
noncomputable section

local instance cuspActual_trueInnerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜 := ℂ) (E := Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)
local instance cuspActual_energyInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspActual_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

theorem gamma0AllHeight_mass_closure_eq (N : ℕ) [NeZero N] :
    gamma0AllHeightEnergyMassSpace N = gamma0AllHeightCuspidalMassSpace N :=
  gamma0AllHeight_mass_closure_eq_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0WeakSolution_mem_allHeight (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    gamma0WeakSolution N f ∈ gamma0AllHeightMeanZeroEnergy N :=
  gamma0WeakSolution_mem_allHeight_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) f hf

def gamma0CuspidalGreen (N : ℕ) [NeZero N] :
    gamma0AllHeightCuspidalMassSpace N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  gamma0CuspidalGreenOfInvariant N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_apply (N : ℕ) [NeZero N]
    (f : gamma0AllHeightCuspidalMassSpace N) :
    (gamma0CuspidalGreen N f).val = gamma0Green N f.val := rfl

theorem gamma0CuspidalGreen_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_selfAdjoint N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_compact N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_injective N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0CuspidalGreen_denseRange (N : ℕ) [NeZero N] :
    DenseRange (gamma0CuspidalGreen N) :=
  gamma0CuspidalGreenOfInvariant_denseRange N (gamma0Green_mem_allHeightCuspidalMassSpace N)

def gamma0FullCuspidalSpectralBasis (N : ℕ) [NeZero N] :
    HilbertBasis (Gamma0AllHeightSpectralIndex N) ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  gamma0FullCuspidalSpectralBasisOfInvariant N (gamma0Green_mem_allHeightCuspidalMassSpace N)

theorem gamma0FullCuspidalSpectralBasis_coe (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    (gamma0FullCuspidalSpectralBasis N i).val = (gamma0AllHeightSpectralBasis N i).val := rfl

theorem gamma0FullCuspidalSpectralBasis_eigen (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) :
    gamma0Green N (gamma0FullCuspidalSpectralBasis N i).val =
      i.1 • (gamma0FullCuspidalSpectralBasis N i).val :=
  gamma0FullCuspidalSpectralBasisOfInvariant_eigen N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i

theorem gamma0AllHeightSpectralEnergy_ambient_weak (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0AllHeightSpectralEnergy N i).val v =
      (i.1.re⁻¹ : ℂ) * inner ℂ (gamma0FullCuspidalSpectralBasis N i).val
        (gamma0EnergyInclusion N v) :=
  gamma0AllHeightSpectralEnergy_ambient_weak_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i v

theorem gamma0AllHeightSpectralEnergy_ambient_gradient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (v : gamma0EnergySpace N) :
    inner ℂ (gamma0EnergyGradient N (gamma0AllHeightSpectralEnergy N i).val)
      (gamma0EnergyGradient N v) =
        (gamma0AllHeightGradientSpectralValue N i : ℂ) *
          inner ℂ (gamma0FullCuspidalSpectralBasis N i).val (gamma0EnergyInclusion N v) :=
  gamma0AllHeightSpectralEnergy_ambient_gradient_of_green_invariant N
    (gamma0Green_mem_allHeightCuspidalMassSpace N) i v

end
end ArtinMatthews
