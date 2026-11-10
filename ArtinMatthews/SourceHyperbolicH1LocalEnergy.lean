module

public import ArtinMatthews.SourceHyperbolicH1LocalTests
public import ArtinMatthews.SourceHyperbolicH1EnergyGraph
public import ArtinMatthews.SourceHyperbolicProductEnergy
public import ArtinMatthews.SourceHyperbolicH1CoreEnergy
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-! The closed Dirichlet graph on an actual open chart domain. -/
namespace ArtinMatthews.SourceHyperbolicGreen
open MeasureTheory
open scoped Topology ContDiff BigOperators Classical InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def h1EnergyCoreLinear : h1Tests ι 2 →ₗ[ℂ] H1EnergySpace ι where
  toFun := h1EnergyCore
  map_add' f g := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (H1Mass ι × H1Gradient ι)).injective
    exact Prod.ext ((h1TestMassLinear ι 2).map_add f g) ((h1TestGradientLinear ι).map_add f g)
  map_smul' c f := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (H1Mass ι × H1Gradient ι)).injective
    exact Prod.ext ((h1TestMassLinear ι 2).map_smul c f) ((h1TestGradientLinear ι).map_smul c f)

def h1LocalEnergySubmodule (U : Set (ProductSpace ι)) : Submodule ℂ (H1EnergySpace ι) :=
  (LinearMap.range (h1EnergyCoreLinear.comp (h1LocalTests U).subtype)).topologicalClosure

abbrev H1LocalEnergy (U : Set (ProductSpace ι)) := h1LocalEnergySubmodule U

instance h1LocalEnergy_complete (U : Set (ProductSpace ι)) : CompleteSpace (H1LocalEnergy U) :=
  (LinearMap.range (h1EnergyCoreLinear.comp (h1LocalTests U).subtype)).isClosed_topologicalClosure.completeSpace_coe

def h1LocalEnergyCore (U : Set (ProductSpace ι)) (f : h1LocalTests U) : H1LocalEnergy U :=
  ⟨h1EnergyCore f.val,(LinearMap.range (h1EnergyCoreLinear.comp (h1LocalTests U).subtype)).le_topologicalClosure ⟨f,rfl⟩⟩

theorem h1LocalEnergyMass_mem (U : Set (ProductSpace ι)) (hU : MeasurableSet U)
    (u : H1LocalEnergy U) : h1EnergyMass ι u.val ∈ h1SupportedMass U := by
  let S := (h1SupportedMass U).comap (h1EnergyMass ι).toLinearMap
  have hS : IsClosed (S : Set (H1EnergySpace ι)) :=
    (h1SupportedMass_isClosed U hU).preimage (h1EnergyMass ι).continuous
  have hle : LinearMap.range (h1EnergyCoreLinear.comp (h1LocalTests U).subtype) ≤ S := by
    rintro _ ⟨f,rfl⟩
    exact (h1LocalTestMass U f).prop
  exact (LinearMap.range (h1EnergyCoreLinear.comp (h1LocalTests U).subtype)).topologicalClosure_minimal hle hS u.prop

def h1LocalEnergyMass (U : Set (ProductSpace ι)) (hU : MeasurableSet U) :
    H1LocalEnergy U →L[ℂ] h1SupportedMass U :=
  ((h1EnergyMass ι).comp (h1LocalEnergySubmodule U).subtypeL).codRestrict
    (h1SupportedMass U) (h1LocalEnergyMass_mem U hU)

def h1LocalEnergyGradient (U : Set (ProductSpace ι)) :
    H1LocalEnergy U →L[ℂ] H1Gradient ι :=
  (h1EnergyGradient ι).comp (h1LocalEnergySubmodule U).subtypeL

theorem h1LocalEnergyMass_injective (U : Set (ProductSpace ι)) (hU : MeasurableSet U) :
    Function.Injective (h1LocalEnergyMass U hU) := by
  intro u v huv
  apply Subtype.ext
  apply h1EnergyMass_injective
  exact congrArg Subtype.val huv

theorem h1LocalEnergyMass_core (U : Set (ProductSpace ι)) (hU : MeasurableSet U)
    (f : h1LocalTests U) : h1LocalEnergyMass U hU (h1LocalEnergyCore U f) = h1LocalTestMass U f := rfl

theorem h1LocalEnergyMass_denseRange (U : Set (ProductSpace ι))
    (hU : IsOpen U) (hUupper : U ⊆ productUpper ι) :
    DenseRange (h1LocalEnergyMass U hU.measurableSet) := by
  apply (h1LocalTestMass_denseRange U hU hUupper).mono
  rintro _ ⟨f,rfl⟩
  exact ⟨h1LocalEnergyCore U f,rfl⟩

theorem h1LocalEnergy_norm_sq (U : Set (ProductSpace ι)) (hU : MeasurableSet U)
    (u : H1LocalEnergy U) :
    ‖u‖^2 = ‖h1LocalEnergyMass U hU u‖^2 + ‖h1LocalEnergyGradient U u‖^2 :=
  h1Energy_norm_sq u.val

def h1LocalDirichletEnergy (U : Set (ProductSpace ι)) (u : H1LocalEnergy U) : ℝ :=
  ‖h1LocalEnergyGradient U u‖^2

theorem h1LocalDirichletEnergy_nonneg (U : Set (ProductSpace ι)) (u : H1LocalEnergy U) :
    0 ≤ h1LocalDirichletEnergy U u := sq_nonneg _

theorem h1LocalDirichletEnergy_core (U : Set (ProductSpace ι)) (f : h1LocalTests U) :
    h1LocalDirichletEnergy U (h1LocalEnergyCore U f) =
      ∫ p, productGradientEnergy f.val p ∂productVolume ι :=
  h1DirichletEnergy_core f.val

end
end ArtinMatthews.SourceHyperbolicGreen
