module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The finite average of a unitary representation is its orthogonal projection. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def sourceFiniteContinuousRepresentation (ρ : G →* (H →L[ℂ] H)) : Representation ℂ G H :=
  (ContinuousLinearMap.toLinearMapRingHom : (H →L[ℂ] H) →+* (H →ₗ[ℂ] H)).toMonoidHom.comp ρ

def sourceFiniteContinuousInvariants (ρ : G →* (H →L[ℂ] H)) : Submodule ℂ H :=
  (sourceFiniteContinuousRepresentation ρ).invariants

theorem sourceFiniteContinuousInvariants_mem (ρ : G →* (H →L[ℂ] H)) (x : H) :
    x ∈ sourceFiniteContinuousInvariants ρ ↔ ∀ g : G, ρ g x = x := Iff.rfl

variable [Fintype G]

def sourceFiniteAverage (ρ : G →* (H →L[ℂ] H)) : H →L[ℂ] H :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g

theorem sourceFiniteAverage_apply (ρ : G →* (H →L[ℂ] H)) (x : H) :
    sourceFiniteAverage ρ x = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g x := by
  simp [sourceFiniteAverage]

theorem sourceFiniteAverage_isProj (ρ : G →* (H →L[ℂ] H)) :
    LinearMap.IsProj (sourceFiniteContinuousInvariants ρ) (sourceFiniteAverage ρ).toLinearMap := by
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero hn
  have he : (sourceFiniteAverage ρ).toLinearMap =
      (sourceFiniteContinuousRepresentation ρ).averageMap := by
    ext x
    simp [sourceFiniteAverage, Representation.averageMap, GroupAlgebra.average,
      sourceFiniteContinuousRepresentation, invOf_eq_inv]
  rw [he, sourceFiniteContinuousInvariants]
  exact Representation.isProj_averageMap _

theorem sourceFiniteAverage_idempotent (ρ : G →* (H →L[ℂ] H)) :
    IsIdempotentElem (sourceFiniteAverage ρ) := by
  apply ContinuousLinearMap.isIdempotentElem_toLinearMap_iff.mp
  exact (sourceFiniteAverage_isProj ρ).isIdempotentElem

theorem sourceFiniteAverage_range (ρ : G →* (H →L[ℂ] H)) :
    (sourceFiniteAverage ρ).range = sourceFiniteContinuousInvariants ρ :=
  (sourceFiniteAverage_isProj ρ).range

theorem sourceFiniteContinuousInvariants_isClosed (ρ : G →* (H →L[ℂ] H)) :
    IsClosed (sourceFiniteContinuousInvariants ρ : Set H) := by
  rw [← sourceFiniteAverage_range ρ]
  exact ContinuousLinearMap.IsIdempotentElem.isClosed_range (sourceFiniteAverage_idempotent ρ)

variable (ρ : G →* (H →L[ℂ] H))

theorem sourceFiniteAverage_inner_invariant (hρ : ∀ g : G, ∀ x : H, ‖ρ g x‖ = ‖x‖) (x y : H)
    (hy : y ∈ sourceFiniteContinuousInvariants ρ) :
    inner ℂ (sourceFiniteAverage ρ x) y = inner ℂ x y := by
  have hfix := (sourceFiniteContinuousInvariants_mem ρ y).mp hy
  have hi (g : G) : inner ℂ (ρ g x) y = inner ℂ x y := by
    let u : H →ₗᵢ[ℂ] H := { toLinearMap := (ρ g).toLinearMap, norm_map' := hρ g }
    have h := u.inner_map_map x y
    change inner ℂ (ρ g x) (ρ g y) = inner ℂ x y at h
    simpa only [hfix g] using h
  have hn : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [sourceFiniteAverage_apply, inner_smul_left, sum_inner, hi, hn]

variable [CompleteSpace H]

instance sourceFiniteContinuousInvariants_complete :
    CompleteSpace (sourceFiniteContinuousInvariants ρ) :=
  (sourceFiniteContinuousInvariants_isClosed ρ).completeSpace_coe

theorem sourceFiniteAverage_eq_starProjection (hρ : ∀ g : G, ∀ x : H, ‖ρ g x‖ = ‖x‖) :
    sourceFiniteAverage ρ = (sourceFiniteContinuousInvariants ρ).starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((sourceFiniteAverage_isProj ρ).map_mem x)
  intro y hy
  rw [inner_sub_left]
  change inner ℂ x y - inner ℂ (sourceFiniteAverage ρ x) y = 0
  rw [sourceFiniteAverage_inner_invariant ρ hρ x y hy, sub_self]

theorem sourceFiniteAverage_norm_le (hρ : ∀ g : G, ∀ x : H, ‖ρ g x‖ = ‖x‖) :
    ‖sourceFiniteAverage ρ‖ ≤ 1 := by
  rw [sourceFiniteAverage_eq_starProjection ρ hρ]
  exact Submodule.starProjection_norm_le _

theorem sourceFiniteAverage_isSymmetric (hρ : ∀ g : G, ∀ x : H, ‖ρ g x‖ = ‖x‖) :
    (sourceFiniteAverage ρ).toLinearMap.IsSymmetric := by
  rw [sourceFiniteAverage_eq_starProjection ρ hρ]
  exact Submodule.starProjection_isSymmetric _

end
end ArtinMatthews
