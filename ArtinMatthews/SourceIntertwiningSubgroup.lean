module

public import Mathlib.RepresentationTheory.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A fixed linear map intertwines on a subgroup. This permits exact
verification on the root, torus-unit and uniformizer generators. -/

namespace ArtinMatthews
noncomputable section

variable {R G V W : Type*} [Semiring R] [Group G]
    [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    (ρ : Representation R G V) (σ : Representation R G W) (f : V →ₗ[R] W)

def sourceIntertwiningSubgroup : Subgroup G where
  carrier := {g | ∀ v, f (ρ g v) = σ g (f v)}
  one_mem' := by intro v; rw [map_one, map_one]; rfl
  mul_mem' := by
    intro g h hg hh v
    simp only [map_mul, Module.End.mul_apply]
    rw [hg, hh]
  inv_mem' := by
    intro g hg v
    have he := hg (ρ g⁻¹ v)
    have hv : ρ g (ρ g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hv] at he
    have ht := congrArg (fun w => σ g⁻¹ w) he
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at ht
    exact ht.symm

theorem sourceIntertwiningSubgroup_mem (g : G) :
    g ∈ sourceIntertwiningSubgroup ρ σ f ↔ ∀ v, f (ρ g v) = σ g (f v) := Iff.rfl

end
end ArtinMatthews
