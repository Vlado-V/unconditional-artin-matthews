module

public import ArtinMatthews.SourceKPCompactGardingCore
public import ArtinMatthews.SourceKPCompactH1ClosedForm
public import ArtinMatthews.SourceKPCompactLocalizedMassCompact


set_option backward.privateInPublic true
@[expose] public section

/-! The closed scalar form has the exact Hardy threshold up to an actual compact mass. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ

theorem sourceKPCompactH1_garding :
    ∃ R C : ℝ, 0 ≤ C ∧ ∀ u : V,
      (InfinitePlace.nrComplexPlaces K : ℝ) * ‖sourceKPCompactH1Mass K hζ u‖^2 ≤
        ‖u‖^2 - ‖sourceKPCompactH1Mass K hζ u‖^2 +
          C*‖sourceKPCompactH1LocalizedMass K hζ R u‖^2 := by
  obtain ⟨C,hC,hη⟩ := sourceKPCompactExhaustion_energy_uniform K hζ
  let r : ℝ := InfinitePlace.nrComplexPlaces K
  let R := Real.exp ((((0 : ℕ)+1 : ℕ) : ℝ)+2)
  let D := r+(Real.pi/2)^2*C
  let j := sourceKPCompactH1Mass K hζ
  let A := sourceKPCompactH1LocalizedMass K hζ R
  have hD : 0 ≤ D := by dsimp only [D,r]; positivity
  refine ⟨R,D,hD,fun u => ?_⟩
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun v : V => r*‖j v‖^2 ≤ ‖v‖^2-‖j v‖^2+D*‖A v‖^2) u ?_ ?_
  · exact isClosed_le ((j.continuous.norm.pow 2).const_mul r)
      (((continuous_norm.pow 2).sub (j.continuous.norm.pow 2)).add ((A.continuous.norm.pow 2).const_mul D))
  · intro f
    have h := sourceKPCompactCore_garding K hζ 0 f.val C (hη (0+1))
    change r * ‖j (sourceKPCompactH1Core K hζ f)‖^2 ≤
      ‖sourceKPCompactH1Core K hζ f‖^2-‖j (sourceKPCompactH1Core K hζ f)‖^2 +
        D * ‖A (sourceKPCompactH1Core K hζ f)‖^2
    have he : ‖f‖^2-‖sourceKPCompactFormCoreMassLinear K hζ f‖^2 =
        ∫ y, sourceKPCompactCoreEnergy K hζ f.val y
          ∂sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ) := by
      rw [sourceKPCompactFormCore_norm_sq]
      ring
    rw [show j = sourceKPCompactH1Mass K hζ from rfl,sourceKPCompactH1Mass_core,
      LinearIsometry.norm_map,he]
    exact h

theorem sourceKPCompactH1_garding_compact :
    ∃ R C : ℝ, 0 ≤ C ∧ IsCompactOperator (sourceKPCompactH1LocalizedMass K hζ R) ∧
      ∀ u : V, (InfinitePlace.nrComplexPlaces K : ℝ) * ‖sourceKPCompactH1Mass K hζ u‖^2 ≤
        (sourceKPCompactH1Dirichlet K hζ u u).re +
          C*‖sourceKPCompactH1LocalizedMass K hζ R u‖^2 := by
  obtain ⟨R,C,hC,h⟩ := sourceKPCompactH1_garding K hζ
  refine ⟨R,C,hC,sourceKPCompactH1LocalizedMass_isCompactOperator K hζ R,fun u => ?_⟩
  rw [sourceKPCompactH1Dirichlet_self]
  exact h u

end
end ArtinMatthews
