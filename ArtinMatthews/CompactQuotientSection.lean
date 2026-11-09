module

public import ArtinMatthews.DiscreteQuotientSlices
public import ArtinMatthews.FiniteMeasurableSection
public import Mathlib.MeasureTheory.Measure.Haar.Quotient


set_option backward.privateInPublic true
@[expose] public section

/-! A compact covering set supplies a measurable fundamental domain
for a discrete subgroup. The domain is contained in the given compact
set, and the quotient is represented exactly once at every point. -/
namespace ArtinMatthews.SourcePhysical

open Set Topology MeasureTheory
open scoped Classical Pointwise
noncomputable section
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable (Γ : Subgroup G)
variable [MeasurableSpace G] [BorelSpace G] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

theorem exists_compact_measurable_quotient_section [DiscreteTopology Γ]
    (C : Set G) (hC : IsCompact C) (hQ : ((↑) : G → G ⧸ Γ) '' C = univ) :
    ∃ D : Set G, MeasurableSet D ∧ D ⊆ C ∧
      InjOn ((↑) : G → G ⧸ Γ) D ∧ ((↑) : G → G ⧸ Γ) '' D = univ := by
  obtain ⟨U, hU, h1, hI⟩ := exists_discrete_quotient_slice Γ
  let T (g : G) : Set G := (fun x => g * x) '' U
  have hT (g : G) : IsOpen (T g) := isOpenMap_mul_left g _ hU
  have hTC : C ⊆ ⋃ g, T g := by
    intro x _
    exact mem_iUnion.mpr ⟨x, 1, h1, mul_one x⟩
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover T hT hTC
  let A (g : G) := C ∩ T g
  let q : G → G ⧸ Γ := (↑)
  obtain ⟨D, hD, hsub, hDinj, him⟩ := exists_measurable_finite_section q
    QuotientGroup.continuous_mk.measurable s A
    (fun g => hC.isClosed.measurableSet.inter (hT g).measurableSet)
    (fun g => quotient_slice_image_measurable Γ (T g) C (hT g) (hI g) hC.isClosed.measurableSet)
    (fun g => (hI g).mono inter_subset_right)
  refine ⟨D, hD, ?_, hDinj, ?_⟩
  · intro x hx
    obtain ⟨g, hg⟩ := mem_iUnion.mp (hsub hx)
    exact (show x ∈ A g.val from hg).1
  · change q '' D = univ
    rw [him]
    apply eq_univ_of_forall
    intro y
    have hy : y ∈ q '' C := by
      change y ∈ ((↑) : G → G ⧸ Γ) '' C
      rw [hQ]
      exact mem_univ _
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨g, hg⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hgs, hxg⟩ := mem_iUnion.mp hg
    exact mem_iUnion.mpr ⟨⟨g, hgs⟩, x, ⟨hx, hxg⟩, rfl⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [BorelSpace G]
  [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)] in
theorem isFundamentalDomain_of_quotient_section (D : Set G) (hD : MeasurableSet D)
    (hI : InjOn ((↑) : G → G ⧸ Γ) D) (hQ : ((↑) : G → G ⧸ Γ) '' D = univ)
    (ν : Measure G) : IsFundamentalDomain Γ.op D ν := by
  apply IsFundamentalDomain.mk' hD.nullMeasurableSet
  intro x
  have hx : ((x : G) : G ⧸ Γ) ∈ ((↑) : G → G ⧸ Γ) '' D := by rw [hQ]; exact mem_univ _
  obtain ⟨y, hy, he⟩ := hx
  have hyx : y / x ∈ Γ := QuotientGroup.eq_iff_div_mem.mp he
  let g : Γ.op := ⟨MulOpposite.op (y / x), hyx⟩
  have hg : g • x = y := by
    change x * (y / x) = y
    rw [mul_comm, div_mul_cancel]
  refine ⟨g, ?_, ?_⟩
  · change g • x ∈ D
    rw [hg]
    exact hy
  intro a ha
  have haQ : ((a • x : G) : G ⧸ Γ) = (y : G ⧸ Γ) := by
    change QuotientGroup.mk' Γ (x * a.val.unop) = QuotientGroup.mk' Γ y
    have hone : QuotientGroup.mk' Γ a.val.unop = 1 := (QuotientGroup.eq_one_iff _).mpr a.property
    rw [map_mul]
    rw [hone, mul_one]
    exact he.symm
  have hax : a • x = y := hI ha hy haQ
  apply Subtype.ext
  apply MulOpposite.unop_injective
  change a.val.unop = y / x
  change x * a.val.unop = y at hax
  rw [← hax, mul_comm, mul_div_cancel_right]

end
end ArtinMatthews.SourcePhysical
