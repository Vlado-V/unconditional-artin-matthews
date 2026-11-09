module

public import ArtinMatthews.SpectralGamma0CuspEigenfunctions
public import ArtinMatthews.SpectralGamma0FormOperator


set_option backward.privateInPublic true
@[expose] public section

/-! Structural consequences of ambient Green preservation of the genuine
all-height cuspidal mass kernel. Preservation is an explicit hypothesis in
this intermediate file; its analytic proof is a separate constant-term
argument. No unconditional full-cuspidal completeness is asserted here. -/
noncomputable section
open Set Topology
namespace ArtinMatthews

local instance cuspCompatibility_trueInnerProduct (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)
local instance cuspCompatibility_energyInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspCompatibility_massInner (N : ℕ) [NeZero N] :
    Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

variable (N : ℕ) [NeZero N]
variable (hG : ∀ f ∈ gamma0AllHeightCuspidalMassSpace N,
  gamma0Green N f ∈ gamma0AllHeightCuspidalMassSpace N)

def gamma0CuspidalGreenOfInvariant :
    gamma0AllHeightCuspidalMassSpace N →L[ℂ] gamma0AllHeightCuspidalMassSpace N :=
  (gamma0Green N).restrict hG

theorem gamma0CuspidalGreenOfInvariant_selfAdjoint :
    IsSelfAdjoint (gamma0CuspidalGreenOfInvariant N hG) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    ((gamma0Green_symmetric N).restrict_invariant hG)

theorem gamma0CuspidalGreenOfInvariant_injective :
    Function.Injective (gamma0CuspidalGreenOfInvariant N hG) := by
  intro f g h
  apply Subtype.ext
  exact gamma0Green_injective N (congrArg Subtype.val h)

theorem gamma0CuspidalGreenOfInvariant_denseRange :
    DenseRange (gamma0CuspidalGreenOfInvariant N hG) :=
  OAI.CoulombAtom.selfAdjoint_denseRange (gamma0CuspidalGreenOfInvariant_selfAdjoint N hG)
    (gamma0CuspidalGreenOfInvariant_injective N hG)

include hG

theorem gamma0WeakSolution_mem_allHeight_of_green_invariant
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    gamma0WeakSolution N f ∈ gamma0AllHeightMeanZeroEnergy N := by
  apply (gamma0EnergyInclusion_mem_cuspidalMass_iff N _).mp
  rw [← gamma0Green_apply]
  exact hG f hf

theorem gamma0AllHeight_mass_closure_eq_of_green_invariant :
    gamma0AllHeightEnergyMassSpace N = gamma0AllHeightCuspidalMassSpace N := by
  apply le_antisymm (gamma0AllHeight_energy_mass_closure_le_cuspidal N)
  intro f hf
  have hproperty : ∀ v : gamma0AllHeightCuspidalMassSpace N,
      v.val ∈ gamma0AllHeightEnergyMassSpace N := by
    apply isClosed_property (gamma0CuspidalGreenOfInvariant_denseRange N hG)
      ((Submodule.isClosed_topologicalClosure _).preimage continuous_subtype_val)
    intro v
    let u : gamma0AllHeightMeanZeroEnergy N :=
      ⟨gamma0WeakSolution N v.val, gamma0WeakSolution_mem_allHeight_of_green_invariant N hG v.val v.property⟩
    apply Submodule.le_topologicalClosure
    refine ⟨u,?_⟩
    exact (gamma0Green_apply N v.val).symm
  exact hproperty ⟨f,hf⟩

theorem gamma0AllHeightWeakSolution_eq_ambient_of_green_invariant
    (f : gamma0AllHeightEnergyMassSpace N) :
    (gamma0AllHeightCoreWeakSolution N f).val = gamma0WeakSolution N f.val := by
  have hf := gamma0AllHeight_energy_mass_closure_le_cuspidal N f.property
  let u : gamma0AllHeightMeanZeroEnergy N :=
    ⟨gamma0WeakSolution N f.val,gamma0WeakSolution_mem_allHeight_of_green_invariant N hG f.val hf⟩
  have hu : u = gamma0AllHeightCoreWeakSolution N f := by
    apply gamma0AllHeightCoreWeakSolution_unique
    intro v
    exact gamma0WeakSolution_equation N f.val v.val
  exact (congrArg Subtype.val hu).symm

theorem gamma0AllHeightGreen_eq_ambient_of_green_invariant
    (f : gamma0AllHeightEnergyMassSpace N) :
    (gamma0AllHeightCoreGreen N f).val = gamma0Green N f.val := by
  change gamma0EnergyInclusion N (gamma0AllHeightCoreWeakSolution N f).val = _
  rw [gamma0AllHeightWeakSolution_eq_ambient_of_green_invariant N hG,gamma0Green_apply]

theorem gamma0CuspidalGreenOfInvariant_compact :
    IsCompactOperator (gamma0CuspidalGreenOfInvariant N hG) := by
  let e := LinearIsometryEquiv.ofEq (gamma0AllHeightEnergyMassSpace N)
    (gamma0AllHeightCuspidalMassSpace N) (gamma0AllHeight_mass_closure_eq_of_green_invariant N hG)
  have he : gamma0CuspidalGreenOfInvariant N hG =
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((gamma0AllHeightCoreGreen N).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Subtype.ext
    change gamma0Green N f.val = (gamma0AllHeightCoreGreen N (e.symm f)).val
    rw [gamma0AllHeightGreen_eq_ambient_of_green_invariant N hG]
    rfl
  rw [he]
  exact ((gamma0AllHeightCoreGreen_compact N).comp_clm
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
      e.toContinuousLinearEquiv.toContinuousLinearMap

end ArtinMatthews
