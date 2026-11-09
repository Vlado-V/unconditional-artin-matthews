module

public import ArtinMatthews.SourceKPAdelicOutgoingExceptionalTrace


set_option backward.privateInPublic true
@[expose] public section

/-! Literal relations in the actual continued negative principal series. -/
namespace ArtinMatthews
open NumberField
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "E" => sourceKPAdelicOutgoingExceptionalSection K hζ
local notation "G" => SourceKPAdelicProjective K hζ
local notation "Π₋" => SourceKPAdelicPrincipalSeries K hζ (-(1/6 : ℂ))
local notation "ρ₋" => sourceKPAdelicPrincipalSeriesRepresentation K hζ (-(1/6 : ℂ))

variable {I : Type} [Fintype I]

def SourceKPResidualOutgoingRelation (t : I → Gf) (c : I → ℂ) : Prop :=
  (∑ i : I, c i • ρ₋ ((1,t i) : G) E) = (0 : Π₋)

theorem sourceKPResidualOutgoingRelation_iff (t : I → Gf) (c : I → ℂ) :
    SourceKPResidualOutgoingRelation K hζ t c ↔ (∑ i : I, c i • ρ₋ ((1,t i) : G) E) = (0 : Π₋) :=
  Iff.rfl

theorem sourceKPResidualOutgoingRelation_scattering_zero
    (t : I → Gf) (c : I → ℂ) (hrel : SourceKPResidualOutgoingRelation K hζ t c) (qf : Gf) :
    (∑ i : I, c i * sourceKPFiniteFiberScatteringResidue K hζ (qf*t i)
      (sourceKPAdelicOutgoingScatteringWindow K hζ (qf*t i))) = 0 := by
  exact sourceKPAdelicOutgoingExceptionalSection_canonical_scattering_relation K hζ t c hrel qf

end
end ArtinMatthews
