module

public import ArtinMatthews.IntegerConductor


set_option backward.privateInPublic true
@[expose] public section

/-! The conductor-zero condition determines the annihilator of the actual
valuation ring.  The converse uses its principal maximal ideal, so no
self-duality hypothesis is inserted. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem inversePrime_div_integral_of_not_integer {a : K}
    (ha : a ∉ (ValuativeRel.valuation K).integer) :
    ∃ r : 𝒪[K], (tameUniformizer K : K) * a⁻¹ = (r : K) := by
  have ha0 : a ≠ 0 := by
    intro he
    apply ha
    rw [he]
    exact (ValuativeRel.valuation K).integer.zero_mem
  have hva : 1 < ValuativeRel.valuation K a := lt_of_not_ge ha
  have hai : ValuativeRel.valuation K a⁻¹ < 1 :=
    (Valuation.one_lt_val_iff (ValuativeRel.valuation K) ha0).mp hva
  let ai : 𝒪[K] := ⟨a⁻¹, hai.le⟩
  have hai_mem : ai ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit ai
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    exact hai
  exact inversePrime_mul_maximal_integral K ai hai_mem

theorem conductorZero_dual_integer (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ) (a : K) :
    (∀ b : 𝒪[K], ψ (a * (b : K)) = 1) ↔ a ∈ (ValuativeRel.valuation K).integer := by
  constructor
  · intro hh
    by_contra ha
    have ha0 : a ≠ 0 := by
      intro he
      apply ha
      rw [he]
      exact (ValuativeRel.valuation K).integer.zero_mem
    obtain ⟨r, hr⟩ := inversePrime_div_integral_of_not_integer K ha
    obtain ⟨z, hz⟩ := hψ.inverse_prime
    have ht := hh (r * z)
    have heq : a * ((r * z : 𝒪[K]) : K) = (tameUniformizer K : K) * (z : K) := by
      change a * ((r : K) * (z : K)) = _
      rw [← hr]
      field_simp
    rw [heq] at ht
    exact hz ht
  · intro ha b
    exact hψ.integer (⟨a, ha⟩ * b)

theorem conductorZero_nontrivial (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ) :
    ∃ a : K, ψ a ≠ 1 := by
  obtain ⟨x, hx⟩ := hψ.inverse_prime
  exact ⟨(tameUniformizer K : K) * (x : K), hx⟩

end

end ArtinMatthews.QuadraticWeil
