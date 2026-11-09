module

public import ArtinMatthews.H1LocalPlateauCutoff
public import ArtinMatthews.SourceKPCompactChartMassLift
public import ArtinMatthews.SourceKPCompactCoreLocalization


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-isotropy saturation of a coordinate plateau. -/
namespace ArtinMatthews
open NumberField Matrix MeasureTheory SourceHyperbolicGreen Filter
open scoped NumberField MatrixGroups AdeleRing Topology ContDiff Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCompactChartPlateau_exists
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    ∃ η : SourceKPFiniteChartTests K hζ b p,
      ∃ W : Set (SourceKPAutomorphicCompactLevel K hζ),
        IsOpen W ∧ sourceKPUpperToCompact K hζ b p ∈ W ∧
        W ⊆ Set.range (sourceKPFiniteChartProjection K hζ b p) ∧
        ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p,
          sourceKPCompactCoordinateProjection K hζ b x ∈ W → η.val.val =ᶠ[𝓝 x] 1 := by
  let U := sourceKPFiniteChartCoordinateDomain K hζ b p
  let c := sourceKPUpperFiniteChart K hζ b p
  let e := sourceKPArchUpperEuclideanMap K
  let π := sourceKPFiniteChartProjection K hζ b p
  let H := SourceKPFiniteChartStabilizer K hζ b p
  obtain ⟨η,_,_,V,hV,hp,hη⟩ := h1LocalPlateauCutoff_exists U
    (sourceKPFiniteChartCoordinateDomain_isOpen K hζ b p)
    (sourceKPFiniteChartCoordinateDomain_upper K hζ b p) (e p)
    (sourceKPFiniteChartCoordinateDomain_mem K hζ b p)
  let O : Set c.domain := {x | ∀ γ : H, e (γ.val • x.val) ∈ V}
  have hO : IsOpen O := by
    have he : O = ⋂ γ : H, (fun x : c.domain => e (γ.val • x.val)) ⁻¹' V := by
      ext x
      simp only [O,Set.mem_setOf_eq,Set.mem_iInter,Set.mem_preimage]
    rw [he]
    apply isOpen_iInter_of_finite
    intro γ
    exact hV.preimage ((sourceKPArchUpperEuclideanMap_continuous K).comp
      ((continuous_const_smul γ.val).comp continuous_subtype_val))
  have hpO : (⟨p,c.center_mem⟩ : c.domain) ∈ O := by
    intro γ
    change e (γ.val • p) ∈ V
    rw [show γ.val • p = p from γ.prop]
    exact hp
  refine ⟨η,π '' O,(sourceKPFiniteChartProjection_isOpenMap K hζ b p) _ hO,
    ⟨⟨p,c.center_mem⟩,hpO,rfl⟩,Set.image_subset_range _ _,?_⟩
  rintro _ ⟨x,hx,rfl⟩ h
  let d : c.domain := ⟨x,hx⟩
  have hd : sourceKPCompactCoordinateProjection K hζ b (e x) = π d := by
    unfold sourceKPCompactCoordinateProjection
    rw [sourceKPArchUpperEuclideanMap_left_inverse]
    rfl
  rw [hd] at h
  obtain ⟨z,hz,heq⟩ := h
  obtain ⟨g,hg,hgx⟩ := (sourceKPUpperToCompact_eq_iff_rational K hζ b b x z.val).mp heq.symm
  let δ : sourceKPArchComponentSubgroup K hζ b :=
    ⟨sourceKPRationalArchMap K hζ g,⟨g,hg,rfl⟩⟩
  have hδ : δ • p = p := by
    by_contra hn
    exact Set.disjoint_left.mp (c.separated δ hn) ⟨z.val,z.prop,hgx⟩ hx
  let γ : H := ⟨δ,hδ⟩
  have hxV : e x ∈ V := by
    have hγ : γ.val • z.val = x := hgx
    rw [← hγ]
    exact hz γ
  filter_upwards [hV.mem_nhds hxV] with y hy
  exact hη y hy

end
end ArtinMatthews
