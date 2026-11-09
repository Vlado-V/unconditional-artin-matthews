module

public import ArtinMatthews.StandardLocalSquareWeil
public import ArtinMatthews.FiniteQuadraticHilbertSign
public import ArtinMatthews.AdicAnalyticWeilCocycle
public import ArtinMatthews.StandardAdelicTracePlaces
public import ArtinMatthews.SLocalHilbertForm


set_option backward.privateInPublic true
@[expose] public section

/-! Outside the actual different and primes above two, the standard
analytic Weil factor has the genuine local Artin-Hilbert defect. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain ClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open GlobalClassFieldTheory.Reciprocity
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField ValuativeRel Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

def standardWeilBadPlaces : Finset (HeightOneSpectrum (𝓞 F)) :=
  StandardAdelic.traceBadPlaces F ∪ powerResidueExponentFinitePlaces F 2

theorem adic_two_eq_one_of_not_mem_exponent (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ powerResidueExponentFinitePlaces F 2) :
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1 := by
  have hnot : (2 : 𝓞 F) ∉ v.asIdeal := by
    intro hm
    apply hv
    rw [mem_powerResidueExponentFinitePlaces_iff, powerResidueExponentIdeal,
      Ideal.dvd_span_singleton]
    exact hm
  have hF := (v.valuation_eq_one_iff_notMem (K := F) (r := (2 : 𝓞 F))).2 hnot
  have hc : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
      (algebraMap F (v.adicCompletion F) (2 : F)) = 1 := by
    change Valued.v ((2 : F) : v.adicCompletion F) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    simpa only [map_ofNat] using hF
  simpa only [map_ofNat] using hc

local instance tameFiniteWeilCharZero (v : HeightOneSpectrum (𝓞 F)) : CharZero (v.adicCompletion F) :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inr v)
local instance tameFiniteWeilMeasurable (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) :=
  borel (v.adicCompletion F)
local instance tameFiniteWeilBorel (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩

theorem standardNormalizedWeil_finite_eq_local (a : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    standardNormalizedWeil F a (.inr v) =
      analyticNormalizedWeil (StandardAdelic.localFiniteCharacter F v)
        (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a) := rfl

theorem standardNormalizedWeil_finite_cocycle (a b : Fˣ) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ standardWeilBadPlaces F) :
    standardNormalizedWeil F a (.inr v) * standardNormalizedWeil F b (.inr v) =
      finiteQuadraticHilbertSign F a b v * standardNormalizedWeil F (a * b) (.inr v) := by
  have hbad : v ∉ StandardAdelic.traceBadPlaces F := fun he => hv (Finset.mem_union_left _ he)
  have hexp : v ∉ powerResidueExponentFinitePlaces F 2 := fun he => hv (Finset.mem_union_right _ he)
  have h := adicAnalyticWeil_cocycle F v (StandardAdelic.localFiniteCharacter F v)
    (StandardAdelic.localFiniteCharacter_conductorZero F v hbad)
    (StandardAdelic.localFiniteCharacter_unitary F v) (StandardAdelic.localFiniteCharacter_continuous F v)
    (adic_two_eq_one_of_not_mem_exponent F v hexp)
    (finitePlaceAdicHilbertPairingFamily F 2 (numberFieldQuadraticRoots F) v)
    (finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 2 (numberFieldQuadraticRoots F) v)
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a)
    (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b)
  rw [← finiteQuadraticHilbertSign_eq_local F a b v,
    ← map_mul (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom)] at h
  rw [← standardNormalizedWeil_finite_eq_local F a v,
    ← standardNormalizedWeil_finite_eq_local F b v,
    ← standardNormalizedWeil_finite_eq_local F (a * b) v] at h
  exact h

end

end ArtinMatthews.QuadraticWeil
