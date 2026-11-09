module

public import ArtinMatthews.SourceKPCompactH1Completion


set_option backward.privateInPublic true
@[expose] public section

/-! A weak equation against genuine compact tests extends to the completed form domain. -/
namespace ArtinMatthews
open NumberField MeasureTheory SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing Topology InnerProductSpace ComplexConjugate
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "V" => SourceKPCompactH1 K hζ
local notation "L" => Lp ℂ 2 (sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ))

theorem sourceKPCompactH1Dirichlet_continuous_right (u : V) :
    Continuous (sourceKPCompactH1Dirichlet K hζ u) :=
  (continuous_const.inner continuous_id).sub
    (continuous_const.inner (sourceKPCompactH1Mass K hζ).continuous)

theorem sourceKPCompactH1Dirichlet_continuous_left (u : V) :
    Continuous (fun v => sourceKPCompactH1Dirichlet K hζ v u) :=
  (continuous_id.inner continuous_const).sub
    ((sourceKPCompactH1Mass K hζ).continuous.inner continuous_const)

theorem sourceKPCompactH1_weak_of_core (u : V) (F : L) (z : ℂ)
    (h : ∀ φ : sourceKPCompactC2Core K hζ,
      sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ ⟨φ⟩) u =
        z * inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) (sourceKPCompactH1Mass K hζ u) +
          inner ℂ (sourceKPCompactCoreMass K hζ 2 φ) F)
    (v : V) :
    sourceKPCompactH1Dirichlet K hζ v u =
      z * inner ℂ (sourceKPCompactH1Mass K hζ v) (sourceKPCompactH1Mass K hζ u) +
        inner ℂ (sourceKPCompactH1Mass K hζ v) F := by
  let j := sourceKPCompactH1Mass K hζ
  refine (sourceKPCompactH1Core_denseRange K hζ).induction_on
    (p := fun w : V => sourceKPCompactH1Dirichlet K hζ w u =
      z * inner ℂ (j w) (j u) + inner ℂ (j w) F) v ?_ ?_
  · exact isClosed_eq (sourceKPCompactH1Dirichlet_continuous_left K hζ u)
      (((j.continuous.inner continuous_const).const_mul z).add (j.continuous.inner continuous_const))
  · intro φ
    change sourceKPCompactH1Dirichlet K hζ (sourceKPCompactH1Core K hζ φ) u =
      z * inner ℂ (sourceKPCompactH1Mass K hζ (sourceKPCompactH1Core K hζ φ)) (j u) +
        inner ℂ (sourceKPCompactH1Mass K hζ (sourceKPCompactH1Core K hζ φ)) F
    rw [sourceKPCompactH1Mass_core]
    exact h φ.val

end
end ArtinMatthews
