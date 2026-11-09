module

public import ArtinMatthews.SourceKPCompactGenuineHeightMass
public import ArtinMatthews.SourceKPCompactRellichChartMeasure
public import ArtinMatthews.SourceKPCompactRellichBounds
public import ArtinMatthews.SourceKPCompactChartPlateau
public import ArtinMatthews.SourceHyperbolicLocalRellich
public import ArtinMatthews.L2FiniteChartCover


set_option backward.privateInPublic true
@[expose] public section

/-! Rellich compactness of the actual compact-sublevel restriction, by finite measured charts. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen Set Filter
open scoped NumberField MatrixGroups AdeleRing Topology ENNReal Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Y" => SourceKPAutomorphicCompactLevel K hζ
local notation "X" => ProductSpace (InfinitePlace K)
local notation "T" => SourceKPCompactFormCore K hζ
local notation "μ" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "ν" => productVolume (InfinitePlace K)
local notation "L" => Lp ℂ 2 μ

theorem sourceKPCompactCoreLocalizedMass_isCompact_closure
    (S : Set Y) (hS : IsCompact S) (r : ℝ) :
    IsCompact (closure ((measurableL2Cutoff μ S hS.measurableSet).comp
      (sourceKPCompactFormCoreMass K hζ) '' Metric.closedBall (0 : T) r)) := by
  classical
  have hchart (y : Y) :
      ∃ (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K)
        (η : SourceKPFiniteChartTests K hζ b p) (W : Set Y),
        IsOpen W ∧ y ∈ W ∧ W ⊆ range (sourceKPFiniteChartProjection K hζ b p) ∧
        ∀ x ∈ sourceKPFiniteChartCoordinateDomain K hζ b p,
          sourceKPCompactCoordinateProjection K hζ b x ∈ W → η.val.val =ᶠ[𝓝 x] 1 := by
    obtain ⟨b, p, rfl⟩ := sourceKPUpperToCompact_cover K hζ y
    obtain ⟨η, W, hW, hyW, hWR, hη⟩ := sourceKPCompactChartPlateau_exists K hζ b p
    exact ⟨b, p, η, W, hW, hyW, hWR, hη⟩
  choose b p η W hW hyW hWR hη using hchart
  obtain ⟨I, hI⟩ := hS.elim_finite_subcover W hW (fun y _ => mem_iUnion.mpr ⟨y, hyW y⟩)
  let J := ↥I
  let A := Metric.closedBall (0 : T) r
  let f (u : A) : L := sourceKPCompactFormCoreMass K hζ u.val
  let q (j : J) : X → Y := sourceKPCompactCoordinateProjection K hζ (b j.val)
  let ρ (j : J) : Measure X := sourceKPCompactRellichChartMeasure K hζ (b j.val) (p j.val)
  let F (j : J) (u : A) : h1Tests (InfinitePlace K) 2 :=
    (sourceKPCompactCoreLocalized K hζ u.val.val (b j.val) (p j.val) (η j.val)).val
  have hcover : S ⊆ ⋃ j : J, W j.val := by
    intro y hy
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hI hy)
    obtain ⟨hjI, hjW⟩ := mem_iUnion.mp hj
    exact mem_iUnion.mpr ⟨⟨j, hjI⟩, hjW⟩
  have hlocal (j : J) : IsCompact (closure (range (fun u : A => h1TestMass (F j u)))) := by
    obtain ⟨M, B, hbound⟩ := sourceKPCompactRellichBounds K hζ (b j.val) (p j.val) (η j.val) r
    exact sourceHyperbolicLocalRellich (F j) (tsupport (η j.val).val.val)
      (η j.val).val.prop.2.1
      ((η j.val).prop.trans (sourceKPFiniteChartCoordinateDomain_upper K hζ (b j.val) (p j.val)))
      (fun u => sourceKPCompactCoreLocalized_support_subset K hζ u.val.val
        (b j.val) (p j.val) (η j.val))
      M B (fun u => (hbound u.val u.prop).1) (fun u => (hbound u.val u.prop).2)
  have hglue := finiteChart_cover_l2_isCompact_closure μ (fun _ : J => X)
    (fun _ => ν) ρ S hS.measurableSet (fun j => W j.val)
    (fun j => (hW j.val).measurableSet) hcover q
    (fun j => sourceKPCompactCoordinateProjection_measurable K hζ (b j.val))
    (fun _ => 1) (fun _ => zero_le_one)
    (fun j => sourceKPCompactRellichChartMeasure_le_volume K hζ (b j.val) (p j.val))
    (by
      intro j
      have hm := (sourceKPCompactCoordinateProjection_measurePreserving K hζ (b j.val) (p j.val)).map_eq
      change Measure.map (q j) (ρ j) =
        (μ).restrict (range (sourceKPFiniteChartProjection K hζ (b j.val) (p j.val))) at hm
      rw [hm, ENNReal.ofReal_one, one_smul]
      exact Measure.restrict_mono (hWR j.val) le_rfl)
    f (fun j u => h1TestMass (F j u))
    (fun j u => sourceKPCompactRellichChartMeasure_localized_ae K hζ (b j.val) (p j.val)
      u.val.val (η j.val) (W j.val) (hη j.val)) hlocal
  have heq : range (fun u : A => measurableL2Cutoff μ S hS.measurableSet (f u)) =
      (measurableL2Cutoff μ S hS.measurableSet).comp (sourceKPCompactFormCoreMass K hζ) '' A := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.prop, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  rw [heq] at hglue
  exact hglue

theorem sourceKPCompactH1LocalizedMass_isCompactOperator (R : ℝ) :
    IsCompactOperator (sourceKPCompactH1LocalizedMass K hζ R) :=
  sourceKPCompactH1LocalizedMass_compact_of_core K hζ R
    (sourceKPCompactCoreLocalizedMass_isCompact_closure K hζ _
      (sourceKPAutomorphicCompactOrbitHeight_sublevel_isCompact K hζ R) 2)

theorem sourceKPCompactGenuineH1LocalizedMass_isCompactOperator (R : ℝ) :
    IsCompactOperator (sourceKPCompactGenuineH1LocalizedMass K hζ R) :=
  (sourceKPCompactH1LocalizedMass_isCompactOperator K hζ R).comp_clm
    (sourceKPCompactGenuineH1 K hζ).subtypeL

end
end ArtinMatthews
