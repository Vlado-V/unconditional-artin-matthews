module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Homeomorph.Quotient
public import Mathlib.Topology.ContinuousMap.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Quotient actions and maps for commuting continuous group actions. -/
namespace ArtinMatthews
open Topology
noncomputable section

variable (Γ M X : Type*) [Group Γ] [Monoid M] [MulAction Γ X] [MulAction M X]
  [SMulCommClass Γ M X]

@[instance_reducible]
def sourceCommutingOrbitAction : MulAction M (Quotient (MulAction.orbitRel Γ X)) where
  smul m := Quotient.map' (m • ·) (by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨γ, (smul_comm γ m y).trans (congrArg (m • ·) hγ)⟩)
  one_smul x := by
    induction x using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (one_smul M x)
  mul_smul m n x := by
    induction x using Quotient.inductionOn with
    | _ x => exact congrArg (Quotient.mk _) (mul_smul m n x)

section Continuous
variable [TopologicalSpace M] [TopologicalSpace X]
  [ContinuousSMul M X] [ContinuousConstSMul Γ X]

local instance : MulAction M (Quotient (MulAction.orbitRel Γ X)) :=
  sourceCommutingOrbitAction Γ M X

theorem sourceCommutingOrbitAction_continuous :
    ContinuousSMul M (Quotient (MulAction.orbitRel Γ X)) := by
  constructor
  rw [← (IsOpenQuotientMap.id.prodMap
    (MulAction.isOpenQuotientMap_quotientMk (Γ := Γ) (T := X))).continuous_comp_iff]
  exact continuous_quot_mk.comp continuous_smul

end Continuous

section Map
variable {Γ X} {Y : Type*} [MulAction Γ Y]

def sourceOrbitMap (f : X → Y) (he : ∀ (γ : Γ) x, f (γ • x) = γ • f x) :
    Quotient (MulAction.orbitRel Γ X) → Quotient (MulAction.orbitRel Γ Y) :=
  Quotient.map' f (by
    intro x y hxy
    obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp hxy
    exact MulAction.mem_orbit_iff.mpr ⟨γ, (he γ y).symm.trans (congrArg f hγ)⟩)

theorem sourceOrbitMap_injective (f : X → Y) (he : ∀ (γ : Γ) x, f (γ • x) = γ • f x)
    (hf : Function.Injective f) : Function.Injective (sourceOrbitMap f he) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      obtain ⟨γ,hγ⟩ := MulAction.mem_orbit_iff.mp (Quotient.exact h)
      apply Quotient.sound
      exact MulAction.mem_orbit_iff.mpr ⟨γ, hf ((he γ y).trans hγ)⟩

variable [TopologicalSpace X] [TopologicalSpace Y]

theorem sourceOrbitMap_continuous (f : X → Y) (he : ∀ (γ : Γ) x, f (γ • x) = γ • f x)
    (hf : Continuous f) : Continuous (sourceOrbitMap f he) :=
  hf.quotient_map' _

theorem sourceOrbitMap_isOpenMap [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
    (f : X → Y) (he : ∀ (γ : Γ) x, f (γ • x) = γ • f x) (hf : IsOpenMap f) :
    IsOpenMap (sourceOrbitMap f he) := by
  intro U hU
  have hset : sourceOrbitMap f he '' U =
      Quotient.mk (MulAction.orbitRel Γ Y) ''
        (f '' ((Quotient.mk (MulAction.orbitRel Γ X)) ⁻¹' U)) := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨x,rfl⟩ := Quotient.mk_surjective x
      exact ⟨f x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨Quotient.mk _ x,hx,rfl⟩
  rw [hset]
  exact isOpenMap_quotient_mk'_mul _ (hf _ (hU.preimage continuous_quot_mk))

theorem sourceOrbitMap_isOpenEmbedding [ContinuousConstSMul Γ X] [ContinuousConstSMul Γ Y]
    (f : X → Y) (he : ∀ (γ : Γ) x, f (γ • x) = γ • f x) (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (sourceOrbitMap f he) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (sourceOrbitMap_continuous f he hf.continuous)
    (sourceOrbitMap_injective f he hf.injective)
    (sourceOrbitMap_isOpenMap f he hf.isOpenMap)

end Map

section QuotientHomeomorph
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

def sourceQuotientHomeomorph (r : Setoid A) (f : C(A,B)) (hf : IsQuotientMap f)
    (hr : ∀ x y, r x y ↔ f x = f y) : Quotient r ≃ₜ B :=
  (Homeomorph.Quotient.congrRight hr).trans hf.homeomorph

@[simp] theorem sourceQuotientHomeomorph_mk (r : Setoid A) (f : C(A,B))
    (hf : IsQuotientMap f) (hr : ∀ x y, r x y ↔ f x = f y) (x : A) :
    sourceQuotientHomeomorph r f hf hr (Quotient.mk r x) = f x := rfl

end QuotientHomeomorph
end
end ArtinMatthews
