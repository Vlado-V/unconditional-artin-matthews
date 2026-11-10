module

public import ArtinMatthews.SpectralGamma0CuspFormSpace
public import OAI.Analysis.CoulombIonization.FormDomain.CoerciveOperator
public import Mathlib.Analysis.InnerProductSpace.Positive


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact Green operator on the closed mass image of the
all-height mean-zero energy space. Dense range is the proved closure-space
density, not an assumed density in a separately defined cuspidal space. -/
noncomputable section
open Set
open scoped InnerProductSpace
namespace ArtinMatthews

local instance cuspFormGreen_energyInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightMeanZeroEnergy N) :=
  (gamma0AllHeightMeanZeroEnergy_innerProductSpace N).toInner
local instance cuspFormGreen_massInner (N : ℕ) [NeZero N] : Inner ℂ (gamma0AllHeightEnergyMassSpace N) :=
  (gamma0AllHeightEnergyMassSpace_innerProductSpace N).toInner

def gamma0AllHeightCoreWeakSolution (N : ℕ) [NeZero N] :
    gamma0AllHeightEnergyMassSpace N →L[ℂ] gamma0AllHeightMeanZeroEnergy N :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0AllHeightMeanZeroEnergy N)
    (F := gamma0AllHeightEnergyMassSpace N) (gamma0AllHeightCoreInclusion N)

theorem gamma0AllHeightCoreWeakSolution_equation (N : ℕ) [NeZero N]
    (F : gamma0AllHeightEnergyMassSpace N) (v : gamma0AllHeightMeanZeroEnergy N) :
    inner ℂ (gamma0AllHeightCoreWeakSolution N F) v =
      inner ℂ F (gamma0AllHeightCoreInclusion N v) := by
  unfold gamma0AllHeightCoreWeakSolution
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem gamma0AllHeightCoreWeakSolution_unique (N : ℕ) [NeZero N]
    (F : gamma0AllHeightEnergyMassSpace N) {u : gamma0AllHeightMeanZeroEnergy N}
    (hu : ∀ v, inner ℂ u v = inner ℂ F (gamma0AllHeightCoreInclusion N v)) :
    u = gamma0AllHeightCoreWeakSolution N F := by
  apply ext_inner_right ℂ
  intro v
  exact (hu v).trans (gamma0AllHeightCoreWeakSolution_equation N F v).symm

def gamma0AllHeightCoreGreen (N : ℕ) [NeZero N] :
    gamma0AllHeightEnergyMassSpace N →L[ℂ] gamma0AllHeightEnergyMassSpace N :=
  (gamma0AllHeightCoreInclusion N).comp (gamma0AllHeightCoreWeakSolution N)

theorem gamma0AllHeightCoreGreen_energy (N : ℕ) [NeZero N]
    (F : gamma0AllHeightEnergyMassSpace N) :
    (inner ℂ F (gamma0AllHeightCoreGreen N F)).re =
      ‖gamma0AllHeightCoreWeakSolution N F‖^2 := by
  change (inner ℂ F (gamma0AllHeightCoreInclusion N (gamma0AllHeightCoreWeakSolution N F))).re = _
  rw [← gamma0AllHeightCoreWeakSolution_equation]
  exact inner_self_eq_norm_sq (𝕜:=ℂ) (gamma0AllHeightCoreWeakSolution N F)

theorem gamma0AllHeightCoreGreen_symmetric (N : ℕ) [NeZero N] :
    (gamma0AllHeightCoreGreen N).IsSymmetric := by
  intro F G
  change inner ℂ (gamma0AllHeightCoreInclusion N (gamma0AllHeightCoreWeakSolution N F)) G =
    inner ℂ F (gamma0AllHeightCoreInclusion N (gamma0AllHeightCoreWeakSolution N G))
  calc
    _ = star (inner ℂ G (gamma0AllHeightCoreInclusion N (gamma0AllHeightCoreWeakSolution N F))) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (gamma0AllHeightCoreWeakSolution N G) (gamma0AllHeightCoreWeakSolution N F)) := by
      rw [gamma0AllHeightCoreWeakSolution_equation]
    _ = inner ℂ (gamma0AllHeightCoreWeakSolution N F) (gamma0AllHeightCoreWeakSolution N G) :=
      inner_conj_symm _ _
    _ = _ := gamma0AllHeightCoreWeakSolution_equation N F _

theorem gamma0AllHeightCoreGreen_selfAdjoint (N : ℕ) [NeZero N] :
    IsSelfAdjoint (gamma0AllHeightCoreGreen N) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (gamma0AllHeightCoreGreen_symmetric N)

theorem gamma0AllHeightCoreGreen_positive (N : ℕ) [NeZero N] :
    (gamma0AllHeightCoreGreen N).IsPositive := by
  refine ⟨gamma0AllHeightCoreGreen_symmetric N, fun F => ?_⟩
  change 0 ≤ (inner ℂ (gamma0AllHeightCoreGreen N F) F).re
  have he := inner_re_symm (𝕜 := ℂ) (gamma0AllHeightCoreGreen N F) F
  change (inner ℂ (gamma0AllHeightCoreGreen N F) F).re =
    (inner ℂ F (gamma0AllHeightCoreGreen N F)).re at he
  rw [he, gamma0AllHeightCoreGreen_energy]
  exact sq_nonneg _

theorem gamma0AllHeightCoreGreen_eq_zero_iff (N : ℕ) [NeZero N]
    (F : gamma0AllHeightEnergyMassSpace N) : gamma0AllHeightCoreGreen N F = 0 ↔ F = 0 := by
  constructor
  · intro h
    have he := gamma0AllHeightCoreGreen_energy N F
    rw [h, inner_zero_right, Complex.zero_re] at he
    have hw : gamma0AllHeightCoreWeakSolution N F = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
    apply (gamma0AllHeightCoreInclusion_denseRange N).eq_of_inner_left ℂ
    intro v
    rw [← gamma0AllHeightCoreWeakSolution_equation, hw]
    rw [inner_zero_left]
    exact inner_zero_left (𝕜 := ℂ) v
  · rintro rfl
    exact map_zero _

theorem gamma0AllHeightCoreGreen_injective (N : ℕ) [NeZero N] :
    Function.Injective (gamma0AllHeightCoreGreen N) := by
  intro F G h
  apply sub_eq_zero.mp
  apply (gamma0AllHeightCoreGreen_eq_zero_iff N (F-G)).mp
  rw [map_sub, h, sub_self]

theorem gamma0AllHeightCoreGreen_compact (N : ℕ) [NeZero N] :
    IsCompactOperator (gamma0AllHeightCoreGreen N) :=
  (gamma0AllHeightCoreInclusion_compact N).comp_clm (gamma0AllHeightCoreWeakSolution N)

end ArtinMatthews
