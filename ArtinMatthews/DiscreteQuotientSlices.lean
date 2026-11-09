module

public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! A discrete subgroup has an open slice at 1, and every translate
of that slice maps injectively and openly to the actual quotient. -/
namespace ArtinMatthews.SourcePhysical

open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Γ : Subgroup G)

theorem exists_discrete_quotient_slice [DiscreteTopology Γ] : ∃ U : Set G,
    IsOpen U ∧ 1 ∈ U ∧ ∀ g : G,
      InjOn ((↑) : G → G ⧸ Γ) ((fun x => g * x) '' U) := by
  have hsing : IsOpen ({1} : Set Γ) := isOpen_discrete _
  rw [isOpen_induced_iff] at hsing
  obtain ⟨V, hV, heV⟩ := hsing
  have h1V : (1 : G) ∈ V := by
    change (1 : Γ) ∈ Subtype.val ⁻¹' V
    rw [heV]
    exact Set.mem_singleton _
  let D : Set (G × G) := (fun p : G × G => p.1 / p.2) ⁻¹' V
  have hD : IsOpen D := hV.preimage continuous_div'
  have h1D : ((1 : G), (1 : G)) ∈ D := by
    change (1 : G) / 1 ∈ V
    rw [div_one]
    exact h1V
  obtain ⟨U₁, U₂, hU₁, hU₂, h1₁, h1₂, hUV⟩ := isOpen_prod_iff.mp hD 1 1 h1D
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨h1₁, h1₂⟩, ?_⟩
  intro g x hx y hy he
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  have hmem : u / v ∈ Γ := by
    have h := QuotientGroup.eq_iff_div_mem.mp he
    simpa only [mul_div_mul_left_eq_div] using h
  have hval : u / v ∈ V := hUV (show (u, v) ∈ U₁ ×ˢ U₂ from ⟨hu.1, hv.2⟩)
  have hh : (⟨u / v, hmem⟩ : Γ) ∈ Subtype.val ⁻¹' V := hval
  rw [heV] at hh
  have h := congrArg Subtype.val (Set.mem_singleton_iff.mp hh)
  change u / v = 1 at h
  rw [div_eq_one.mp h]

theorem quotient_slice_isOpenEmbedding (U : Set G) (hU : IsOpen U)
    (hi : InjOn ((↑) : G → G ⧸ Γ) U) :
    IsOpenEmbedding (fun x : U => ((x.val : G) : G ⧸ Γ)) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact QuotientGroup.continuous_mk.comp continuous_subtype_val
  · intro x y h
    exact Subtype.ext (hi x.property y.property h)
  · exact QuotientGroup.isOpenMap_coe.comp hU.isOpenMap_subtype_val

variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

theorem quotient_slice_image_measurable (U C : Set G) (hU : IsOpen U)
    (hi : InjOn ((↑) : G → G ⧸ Γ) U) (hC : MeasurableSet C) :
    MeasurableSet (((↑) : G → G ⧸ Γ) '' (C ∩ U)) := by
  let f : U → G ⧸ Γ := fun x => (x.val : G)
  have hf : MeasurableEmbedding f := (quotient_slice_isOpenEmbedding Γ U hU hi).measurableEmbedding
  have h := hf.measurableSet_image' (measurable_subtype_coe hC)
  have he : f '' (Subtype.val ⁻¹' C) = ((↑) : G → G ⧸ Γ) '' (C ∩ U) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, ⟨hx, x.property⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hu⟩, rfl⟩
      exact ⟨⟨x, hu⟩, hx, rfl⟩
  rwa [he] at h

end
end ArtinMatthews.SourcePhysical
