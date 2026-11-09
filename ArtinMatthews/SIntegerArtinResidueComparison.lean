module

public import ArtinMatthews.SIntegerAdicResidueMap
public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison


set_option backward.privateInPublic true
@[expose] public section

/-! Actual comparison of the norm-completion integer ring used by CFT
and the adic integer ring used by the standard additive character.
No definitional equality of the two local field models is assumed. -/
namespace ArtinMatthews.SIntegerAdicResidue

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticWeil
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local instance comparisonAdicRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P
local instance comparisonAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

def artinAdicIntegerEquiv :
    𝒪[ChosenFinitePlaceBaseCompletion (K := K) P] ≃+* 𝒪[P.adicCompletion K] :=
  (finitePlaceCompletionIntegerRingEquiv P).trans
    (RingEquiv.subringCongr (adic_integer_eq K P).symm)

theorem artinAdicIntegerEquiv_global (x : 𝓞 K) :
    artinAdicIntegerEquiv K P (finitePlaceIntegerToCompletion P x) = adicIntegralOfInteger K P x := by
  apply Subtype.ext
  change finitePlaceCompletionRingEquiv P
    (algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) P) (x : K)) =
      algebraMap (𝓞 K) (P.adicCompletion K) x
  rw [finitePlaceCompletionRingEquiv_toCompletion]
  change algebraMap K (P.adicCompletion K) (algebraMap (𝓞 K) K x) = _
  exact (IsScalarTower.algebraMap_apply (𝓞 K) K (P.adicCompletion K) x).symm

def artinAdicResidueEquiv :
    𝓀[ChosenFinitePlaceBaseCompletion (K := K) P] ≃+* 𝓀[P.adicCompletion K] :=
  IsLocalRing.ResidueField.mapEquiv (artinAdicIntegerEquiv K P)

theorem artinAdicResidueEquiv_global (x : 𝓞 K) :
    artinAdicResidueEquiv K P
      (IsLocalRing.residue 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]
        (finitePlaceIntegerToCompletion P x)) = adicResidueOfInteger K P x := by
  change IsLocalRing.residue 𝒪[P.adicCompletion K]
    (artinAdicIntegerEquiv K P (finitePlaceIntegerToCompletion P x)) = _
  rw [artinAdicIntegerEquiv_global]
  rfl

theorem artinAdicResidueEquiv_idealResidue :
    (finitePlaceIdealResidueEquivCompletion P).trans (artinAdicResidueEquiv K P) =
      adicIntegerResidueEquiv K P := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingEquiv.trans_apply, finitePlaceIdealResidueEquivCompletion_apply_mk,
    adicIntegerResidueEquiv_mk]
  exact artinAdicResidueEquiv_global K P x

end
end ArtinMatthews.SIntegerAdicResidue
