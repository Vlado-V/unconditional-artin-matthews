module

public import ArtinMatthews.SIntegerArtinResidueComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PowerResidueReciprocity


set_option backward.privateInPublic true
@[expose] public section

/-! Actual S-integers and their units in the norm-completion frame used
by the local Artin map. All residue comparisons use the constructed
completion equivalences rather than an identification of field models. -/
namespace ArtinMatthews.SIntegerAdicResidue

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open GlobalClassFieldTheory.Reciprocity
open ArtinMatthews.QuadraticWeil ArtinMatthews.SIntegerPrincipalization ArtinMatthews.SIntegerQuotient
open scoped NumberField ValuativeRel Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : HeightOneSpectrum (𝓞 K))

local instance artinUnitAdicRelation : ValuativeRel (P.adicCompletion K) := adicRelation K P
local instance artinUnitAdicLocalField : IsNonarchimedeanLocalField (P.adicCompletion K) := adicLocalField K P

def artinIntegralOfSInteger (hP : P ∉ principalizingSet S₀) :
    PrincipalIntegerRing S₀ →+* 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P] :=
  (artinAdicIntegerEquiv K P).symm.toRingHom.comp (adicIntegralOfSInteger K S₀ P hP)

theorem artinIntegralOfSInteger_val (hP : P ∉ principalizingSet S₀) (x : PrincipalIntegerRing S₀) :
    (artinIntegralOfSInteger K S₀ P hP x : ChosenFinitePlaceBaseCompletion (K := K) P) =
      algebraMap K (ChosenFinitePlaceBaseCompletion (K := K) P) (x : K) := by
  apply (finitePlaceCompletionRingEquiv P).injective
  have he := congrArg (fun z : 𝒪[P.adicCompletion K] => (z : P.adicCompletion K))
    ((artinAdicIntegerEquiv K P).apply_symm_apply (adicIntegralOfSInteger K S₀ P hP x))
  change finitePlaceCompletionRingEquiv P (artinIntegralOfSInteger K S₀ P hP x) =
    algebraMap K (P.adicCompletion K) (x : K) at he
  rw [he, finitePlaceCompletionRingEquiv_toCompletion]
  rfl

def artinResidueOfSInteger (hP : P ∉ principalizingSet S₀) :
    PrincipalIntegerRing S₀ →+* 𝓀[ChosenFinitePlaceBaseCompletion (K := K) P] :=
  (IsLocalRing.residue 𝒪[ChosenFinitePlaceBaseCompletion (K := K) P]).comp
    (artinIntegralOfSInteger K S₀ P hP)

theorem artinResidueOfSInteger_compare (hP : P ∉ principalizingSet S₀)
    (x : PrincipalIntegerRing S₀) :
    artinAdicResidueEquiv K P (artinResidueOfSInteger K S₀ P hP x) =
      adicResidueOfSInteger K S₀ P hP x := by
  change IsLocalRing.residue 𝒪[P.adicCompletion K]
    (artinAdicIntegerEquiv K P ((artinAdicIntegerEquiv K P).symm (adicIntegralOfSInteger K S₀ P hP x))) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem artinResidueOfSInteger_generator_compare (hP : P ∉ principalizingSet S₀)
    (a : PrincipalIntegerRing S₀)
    (ha : P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀)) = Ideal.span {a})
    (x : PrincipalIntegerRing S₀) :
    artinResidueOfSInteger K S₀ P hP x = finitePlaceIdealResidueEquivCompletion P
      (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x)) := by
  apply (artinAdicResidueEquiv K P).injective
  rw [artinResidueOfSInteger_compare, adicResidueOfSInteger_generator_compare K S₀ P hP a ha]
  exact (congrArg (fun e : ((𝓞 K) ⧸ P.asIdeal) ≃+* 𝓀[P.adicCompletion K] =>
    e (generatorResidueEquiv S₀ P hP a ha (Ideal.Quotient.mk _ x)))
    (artinAdicResidueEquiv_idealResidue K P)).symm

theorem artinIntegralOfSInteger_isUnit (hP : P ∉ principalizingSet S₀)
    (x : PrincipalIntegerRing S₀)
    (hx : x ∉ P.asIdeal.map (algebraMap (𝓞 K) (PrincipalIntegerRing S₀))) :
    IsUnit (artinIntegralOfSInteger K S₀ P hP x) :=
  (adicIntegralOfSInteger_isUnit K S₀ P hP x hx).map (artinAdicIntegerEquiv K P).symm

theorem artinResidueEquiv_eq_powerResidueEquiv :
    finitePlaceIdealResidueEquivCompletion P = finitePlacePrimeResidueEquivLocalResidue K P := by
  ext z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [finitePlaceIdealResidueEquivCompletion_apply_mk, finitePlacePrimeResidueEquivLocalResidue_mk]
  congr 1

end
end ArtinMatthews.SIntegerAdicResidue
