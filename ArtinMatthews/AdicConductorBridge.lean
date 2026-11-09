module

public import ArtinMatthews.IntegerConductorDual
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology


set_option backward.privateInPublic true
@[expose] public section

/-! Conductor-zero data on the actual number-field adic completion, with the
valuation-integer and Mathlib adic-integer models identified explicitly. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open scoped NumberField ValuativeRel Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

@[instance_reducible]
def adicRelation : ValuativeRel (v.adicCompletion F) :=
  ValuativeRel.ofValuation
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))

theorem adicLocalField :
    @IsNonarchimedeanLocalField (v.adicCompletion F) inferInstance
      (adicRelation F v) inferInstance := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.IsNontrivial := inferInstance
  let : ValuativeRel C := adicRelation F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  let : ValuativeRel.IsNontrivial C :=
    (ValuativeRel.isNontrivial_iff_isNontrivial ν).mpr inferInstance
  let : IsValuativeTopology C :=
    isValuativeTopology_of_valued_ofValuation C (WithZero (Multiplicative ℤ))
  exact { toIsValuativeTopology := inferInstance
          toLocallyCompactSpace := inferInstance
          toIsNontrivial := inferInstance }

theorem adic_integer_eq :
    letI : ValuativeRel (v.adicCompletion F) := adicRelation F v
    (ValuativeRel.valuation (v.adicCompletion F)).integer =
      (v.adicCompletionIntegers F).toSubring := by
  let : ValuativeRel (v.adicCompletion F) := adicRelation F v
  let ν : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  ext x
  change ValuativeRel.valuation (v.adicCompletion F) x ≤ 1 ↔ ν x ≤ 1
  calc
    _ ↔ x ≤ᵥ (1 : v.adicCompletion F) := by
      simpa only [map_one] using
        (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation (v.adicCompletion F)) x 1).symm
    _ ↔ _ := by
      simpa only [map_one] using (Valuation.Compatible.vle_iff_le (v := ν) x 1)

theorem adic_mem_integer_iff (x : v.adicCompletion F) :
    letI : ValuativeRel (v.adicCompletion F) := adicRelation F v
    x ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer ↔
      x ∈ v.adicCompletionIntegers F := by
  let : ValuativeRel (v.adicCompletion F) := adicRelation F v
  exact Eq.to_iff (congrArg (fun R : Subring (v.adicCompletion F) => x ∈ R) (adic_integer_eq F v))

def adicConductorZero (ψ : AddChar (v.adicCompletion F) ℂ) : Prop :=
  letI : ValuativeRel (v.adicCompletion F) := adicRelation F v
  letI : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
  ConductorZero (v.adicCompletion F) ψ

theorem adicConductorZero_integer (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ : adicConductorZero F v ψ) (x : v.adicCompletion F)
    (hx : x ∈ v.adicCompletionIntegers F) : ψ x = 1 := by
  let : ValuativeRel (v.adicCompletion F) := adicRelation F v
  let : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
  have hx' : x ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer :=
    (adic_mem_integer_iff F v x).mpr hx
  exact hψ.integer ⟨x, hx'⟩

theorem adicConductorZero_dual (ψ : AddChar (v.adicCompletion F) ℂ)
    (hψ : adicConductorZero F v ψ) (a : v.adicCompletion F) :
    (∀ x ∈ v.adicCompletionIntegers F, ψ (a * x) = 1) ↔
      a ∈ v.adicCompletionIntegers F := by
  let : ValuativeRel (v.adicCompletion F) := adicRelation F v
  let : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
  constructor
  · intro hh
    have hcanonical : a ∈ (ValuativeRel.valuation (v.adicCompletion F)).integer := by
      apply (conductorZero_dual_integer (v.adicCompletion F) ψ hψ a).mp
      intro b
      apply hh
      exact (adic_mem_integer_iff F v (b : v.adicCompletion F)).mp b.property
    exact (adic_mem_integer_iff F v a).mp hcanonical
  · intro ha x hx
    exact adicConductorZero_integer F v ψ hψ (a * x)
      ((v.adicCompletionIntegers F).toSubring.mul_mem ha hx)

end

end ArtinMatthews.QuadraticWeil
