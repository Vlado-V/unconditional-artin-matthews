module

public import ArtinMatthews.AdicConductorBridge


set_option backward.privateInPublic true
@[expose] public section

/-! Transfer a conductor witness from any actual adic prime element to
our canonically chosen inverse uniformizer. No equality of choices is assumed. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField IsDedekindDomain LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ArtinMatthews.QuadraticGauss
open scoped NumberField ValuativeRel Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem adic_chosenPrime_div_prime_integral (u : v.adicCompletion F)
    (hu : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u =
      WithZero.exp (-1 : ℤ)) :
    letI : ValuativeRel (v.adicCompletion F) := adicRelation F v
    letI : IsNonarchimedeanLocalField (v.adicCompletion F) := adicLocalField F v
    ((chosenIntegerRingUniformizer (v.adicCompletion F) : v.adicCompletion F) * u⁻¹) ∈
      (ValuativeRel.valuation (v.adicCompletion F)).integer := by
  let C := v.adicCompletion F
  let ν : Valuation C (WithZero (Multiplicative ℤ)) := Valued.v
  let : ValuativeRel C := adicRelation F v
  let : IsNonarchimedeanLocalField C := adicLocalField F v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  let p : 𝒪[C] := chosenIntegerRingUniformizer C
  have hp : ValuativeRel.valuation C (p : C) < 1 :=
    Valuation.integer.v_irreducible_lt_one (chosenIntegerRingUniformizer_irreducible C)
  have hp' : ν (p : C) < 1 := by
    exact (Valuation.vlt_one_iff ν).mp
      ((Valuation.vlt_one_iff (ValuativeRel.valuation C)).mpr hp)
  have hbound : ν (p : C) ≤ WithZero.exp (-1 : ℤ) := by
    by_cases hz : ν (p : C) = 0
    · simp [hz]
    · apply WithZero.le_exp_of_log_le
      have hlog : WithZero.log (ν (p : C)) < (0 : ℤ) := by
        exact (WithZero.log_lt_iff_lt_exp hz).mpr (by simpa only [WithZero.exp_zero] using hp')
      omega
  apply (adic_mem_integer_iff F v _).mpr
  change ν ((p : C) * u⁻¹) ≤ 1
  rw [map_mul, map_inv₀, hu]
  exact mul_inv_le_one_of_le₀ hbound zero_le

theorem adicConductorZero_of_uniformizer (ψ : AddChar (v.adicCompletion F) ℂ)
    (hint : ∀ x ∈ v.adicCompletionIntegers F, ψ x = 1)
    (u : v.adicCompletion F)
    (hu : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) u =
      WithZero.exp (-1 : ℤ))
    (hw : ∃ x ∈ v.adicCompletionIntegers F, ψ (u⁻¹ * x) ≠ 1) :
    adicConductorZero F v ψ := by
  let C := v.adicCompletion F
  let : ValuativeRel C := adicRelation F v
  let : IsNonarchimedeanLocalField C := adicLocalField F v
  refine ⟨?_, ?_⟩
  · intro x
    exact hint x ((adic_mem_integer_iff F v x).mp x.property)
  · obtain ⟨x, hx, hw⟩ := hw
    let p : 𝒪[C] := chosenIntegerRingUniformizer C
    have hr : (p : C) * u⁻¹ ∈ (ValuativeRel.valuation C).integer :=
      adic_chosenPrime_div_prime_integral F v u hu
    let r : 𝒪[C] := ⟨(p : C) * u⁻¹, hr⟩
    let z : 𝒪[C] := ⟨x, (adic_mem_integer_iff F v x).mpr hx⟩
    refine ⟨r * z, ?_⟩
    have hp0 : (p : C) ≠ 0 := (integerRingUniformizerFieldUnit C).ne_zero
    have heq : (tameUniformizer C : C) * ((r * z : 𝒪[C]) : C) = u⁻¹ * x := by
      change (p : C)⁻¹ * (((p : C) * u⁻¹) * x) = _
      rw [← mul_assoc, inv_mul_cancel_left₀ hp0]
    rwa [heq]

end

end ArtinMatthews.QuadraticWeil
