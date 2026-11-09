module

public import ArtinMatthews.SpectralGamma0EnergyGraph
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual weak inverse of the constructed Γ₀(N) mass-plus-gradient form.
This reuses the dimension-independent Riesz/adjoint argument of math-main's
CubicThetaGlobalWeakInverse and CubicThetaGlobalGreen, with the genuine H²
energy completion substituted.  No compactness, spectral basis, or Kuznetsov
formula is asserted here.
-/

noncomputable section
open scoped InnerProduct

namespace ArtinMatthews

/-- Riesz representation on the actual completed energy space. -/
def gamma0WeakSolution (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) : gamma0EnergySpace N :=
  (InnerProductSpace.toDual ℂ (gamma0EnergySpace N)).symm
    ((innerSL ℂ F).comp (gamma0EnergyInclusion N))

theorem gamma0WeakSolution_equation (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N)
    (v : gamma0EnergySpace N) :
    inner ℂ (gamma0WeakSolution N F) v = inner ℂ F (gamma0EnergyInclusion N v) :=
  InnerProductSpace.toDual_symm_apply

theorem gamma0WeakSolution_unique (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N)
    {u : gamma0EnergySpace N}
    (hu : ∀ v, inner ℂ u v = inner ℂ F (gamma0EnergyInclusion N v)) :
    u = gamma0WeakSolution N F := by
  apply (InnerProductSpace.toDual ℂ (gamma0EnergySpace N)).injective
  ext v
  simpa [gamma0WeakSolution] using hu v

theorem gamma0WeakSolution_eq_adjoint (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) :
    gamma0WeakSolution N F = (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0EnergySpace N)
    (F := Gamma0RegionL2 N) (gamma0EnergyInclusion N)) F := by
  symm
  apply gamma0WeakSolution_unique N F
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]

theorem gamma0WeakSolution_bound (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) :
    ‖gamma0WeakSolution N F‖ ≤ ‖F‖ := by
  rw [gamma0WeakSolution_eq_adjoint]
  calc
    _ ≤ ‖(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0EnergySpace N)
    (F := Gamma0RegionL2 N) (gamma0EnergyInclusion N))‖ * ‖F‖ :=
      (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0EnergySpace N)
    (F := Gamma0RegionL2 N) (gamma0EnergyInclusion N)).le_opNorm F
    _ ≤ 1 * ‖F‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right (gamma0EnergyInclusion_norm N) (norm_nonneg F)
    _ = _ := one_mul _

/-- The actual bounded Green operator of the completed mass-plus-energy form. -/
def gamma0Green (N : ℕ) [NeZero N] : Gamma0RegionL2 N →L[ℂ] Gamma0RegionL2 N :=
  (gamma0EnergyInclusion N).comp (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := gamma0EnergySpace N)
    (F := Gamma0RegionL2 N) (gamma0EnergyInclusion N))

theorem gamma0Green_apply (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) :
    gamma0Green N F = gamma0EnergyInclusion N (gamma0WeakSolution N F) := by
  rw [gamma0WeakSolution_eq_adjoint]
  rfl

theorem gamma0Green_norm (N : ℕ) [NeZero N] : ‖gamma0Green N‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro F
  rw [gamma0Green_apply]
  simpa only [one_mul] using (gamma0EnergyInclusion_bound N _).trans
    (gamma0WeakSolution_bound N F)


theorem gamma0Green_energy (N : ℕ) [NeZero N] (F : Gamma0RegionL2 N) :
    (inner ℂ F (gamma0Green N F)).re = ‖gamma0WeakSolution N F‖ ^ 2 := by
  rw [gamma0Green_apply, ← gamma0WeakSolution_equation]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (gamma0WeakSolution N F)

/-- Symmetry follows directly from the proved weak energy equation. -/
theorem gamma0Green_symmetric (N : ℕ) [NeZero N] : (gamma0Green N).IsSymmetric := by
  intro F G
  change inner ℂ (gamma0Green N F) G = inner ℂ F (gamma0Green N G)
  rw [gamma0Green_apply, gamma0Green_apply]
  calc
    inner ℂ (gamma0EnergyInclusion N (gamma0WeakSolution N F)) G =
        star (inner ℂ G (gamma0EnergyInclusion N (gamma0WeakSolution N F))) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (gamma0WeakSolution N G) (gamma0WeakSolution N F)) := by
      rw [gamma0WeakSolution_equation]
    _ = inner ℂ (gamma0WeakSolution N F) (gamma0WeakSolution N G) := inner_conj_symm _ _
    _ = _ := gamma0WeakSolution_equation N F _

theorem gamma0Green_positive (N : ℕ) [NeZero N] : (gamma0Green N).IsPositive := by
  refine ⟨gamma0Green_symmetric N, fun F => ?_⟩
  change 0 ≤ (inner ℂ (gamma0Green N F) F).re
  have he : (inner ℂ (gamma0Green N F) F).re = (inner ℂ F (gamma0Green N F)).re :=
    inner_re_symm (𝕜 := ℂ) (gamma0Green N F) F
  rw [he, gamma0Green_energy]
  exact sq_nonneg _

end ArtinMatthews
