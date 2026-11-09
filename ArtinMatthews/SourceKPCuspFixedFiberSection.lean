module

public import ArtinMatthews.SourceKPCuspFundamentalSection
public import ArtinMatthews.SourceKPCuspFiniteFiberCover


set_option backward.privateInPublic true
@[expose] public section

/-! The measurable exact high section can be chosen in the same fixed finite
set of actual level fibers at every height. -/
namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory Set
open scoped NumberField MatrixGroups AdeleRing

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCuspFixedFiniteFibers_exists_section (v₀ : InfinitePlace K) (T : ℝ) :
    ∃ F : Set (SourceKPHighCuspFinite K hζ T),
      MeasurableSet F ∧
      (∀ x ∈ F, x.val.2 ∈ sourceKPCuspFixedFiniteFibers K hζ v₀) ∧
      Set.InjOn (sourceKPHighCuspProjection K hζ T) F ∧
      sourceKPHighCuspProjection K hζ T '' F = Set.univ := by
  let C : Set (SourceKPHighCuspFinite K hζ T) :=
    {x | x.val.2 ∈ sourceKPCuspFixedFiniteFibers K hζ v₀}
  have hc : MeasurableSet C := by
    have h : Continuous (fun x : SourceKPHighCuspFinite K hζ T => x.val.2) :=
      continuous_snd.comp continuous_subtype_val
    exact (isOpen_discrete (sourceKPCuspFixedFiniteFibers K hζ v₀)).measurableSet.preimage h.measurable
  have hcover : sourceKPHighCuspProjection K hζ T '' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x,hx⟩ := sourceKPHighCusp_representative K hζ T q
    obtain ⟨γ,hγ⟩ := sourceKPCuspFixedFiniteFibers_representative K hζ v₀ T x
    exact ⟨γ • x,hγ,(sourceKPCuspHighProjection_rational K hζ T γ x).trans hx⟩
  obtain ⟨F,hF,hsub,hinj,hproj⟩ := sourceKPCuspHighProjection_exists_section K hζ T C hc hcover
  exact ⟨F,hF,fun x hx => hsub hx,hinj,hproj⟩

end
end ArtinMatthews
