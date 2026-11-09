module

public import ArtinMatthews.AdicPrimeQuadraticGaussian
public import ArtinMatthews.StandardTameFiniteWeil


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine valuation unit contributes one to the standard analytic
Weil product outside the different and the primes over two. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField ValuativeRel Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F))

local instance finiteUnitRelation : ValuativeRel (P.adicCompletion F) := adicRelation F P
local instance finiteUnitLocalField : IsNonarchimedeanLocalField (P.adicCompletion F) := adicLocalField F P
local instance finiteUnitMeasurable : MeasurableSpace (P.adicCompletion F) := borel (P.adicCompletion F)
local instance finiteUnitBorel : BorelSpace (P.adicCompletion F) := ⟨rfl⟩
local instance finiteUnitResidueFintype : Fintype 𝓀[P.adicCompletion F] := Fintype.ofFinite _

theorem adicUnit_normalizedWeil_eq_one
    (ψ : AddChar (P.adicCompletion F) ℂ) (hψ : adicConductorZero F P ψ)
    (hu : ∀ x, ‖ψ x‖ = 1) (hc : Continuous ψ)
    (h2 : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) 2 = 1)
    (a : (P.adicCompletion F)ˣ)
    (ha : (Valued.v : Valuation (P.adicCompletion F) (WithZero (Multiplicative ℤ))) (a : P.adicCompletion F) = 1) :
    analyticNormalizedWeil ψ a = 1 := by
  let C := P.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  have hva : ValuativeRel.valuation C (a : C) = 1 := by
    have hrel : (a : C) =ᵥ (1 : C) :=
      (Valuation.veq_iff_eq ν).mpr (by simpa only [map_one] using ha)
    simpa only [map_one] using (Valuation.veq_iff_eq (ValuativeRel.valuation C)).mp hrel
  let x : 𝒪[C] := ⟨(a : C), hva.le⟩
  have hx : IsUnit x :=
    (Valuation.integer.integers (ValuativeRel.valuation C)).isUnit_iff_valuation_eq_one.mpr hva
  obtain ⟨u, hu_eq⟩ := hx
  have heu : integerUnitsToFieldUnits C u = a := by
    apply Units.ext
    exact congrArg (fun z : 𝒪[C] => (z : C)) hu_eq
  have he := adic_normalizedAnalyticWeil_eq_tame F P ψ hψ hu hc h2 a
  change analyticNormalizedWeil ψ a = _ at he
  rw [he, ← heu, localTameGaussSection_unit]

theorem standardNormalizedWeil_finite_unit (a : Fˣ)
    (hP : P ∉ standardWeilBadPlaces F) (ha : P.valuation F (a : F) = 1) :
    standardNormalizedWeil F a (.inr P) = 1 := by
  have hbad : P ∉ StandardAdelic.traceBadPlaces F :=
    fun h => hP (Finset.mem_union_left _ h)
  have htwo : P ∉ GlobalClassFieldTheory.Reciprocity.powerResidueExponentFinitePlaces F 2 :=
    fun h => hP (Finset.mem_union_right _ h)
  rw [standardNormalizedWeil_finite_eq_local]
  apply adicUnit_normalizedWeil_eq_one F P (StandardAdelic.localFiniteCharacter F P)
    (StandardAdelic.localFiniteCharacter_conductorZero F P hbad)
    (StandardAdelic.localFiniteCharacter_unitary F P)
    (StandardAdelic.localFiniteCharacter_continuous F P)
    (adic_two_eq_one_of_not_mem_exponent F P htwo)
  change Valued.v ((a : F) : P.adicCompletion F) = 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact ha

end

end ArtinMatthews.QuadraticWeil
