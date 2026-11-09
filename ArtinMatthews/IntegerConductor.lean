module

public import ArtinMatthews.LocalTameGaussSection


set_option backward.privateInPublic true
@[expose] public section

/-! A conductor-zero local additive character descends, after multiplication
by the inverse prime element, to a genuine nontrivial residue character. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

structure ConductorZero (ψ : AddChar K ℂ) : Prop where
  integer : ∀ x : 𝒪[K], ψ (x : K) = 1
  inverse_prime : ∃ x : 𝒪[K], ψ ((tameUniformizer K : K) * (x : K)) ≠ 1

theorem inversePrime_mul_maximal_integral (x : 𝒪[K]) (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) :
    ∃ z : 𝒪[K], (tameUniformizer K : K) * (x : K) = (z : K) := by
  rw [chosenIntegerRingUniformizer_maximalIdeal_eq, Ideal.mem_span_singleton] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  have hzk := congrArg (fun a : 𝒪[K] => (a : K)) hz
  change (x : K) = (chosenIntegerRingUniformizer K : K) * (z : K) at hzk
  rw [hzk]
  change (chosenIntegerRingUniformizer K : K)⁻¹ *
    ((chosenIntegerRingUniformizer K : K) * (z : K)) = (z : K)
  exact inv_mul_cancel_left₀ (integerRingUniformizerFieldUnit K).ne_zero _

def integerShiftCharacter (ψ : AddChar K ℂ) : AddChar 𝒪[K] ℂ where
  toFun x := ψ ((tameUniformizer K : K) * (x : K))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    change ψ ((tameUniformizer K : K) * ((x : K) + (y : K))) = _
    rw [mul_add, ψ.map_add_eq_mul]

theorem integerShiftCharacter_maximal (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (x : 𝒪[K]) (hx : x ∈ (𝓂[K] : Ideal 𝒪[K])) :
    integerShiftCharacter K ψ x = 1 := by
  obtain ⟨z, hz⟩ := inversePrime_mul_maximal_integral K x hx
  change ψ ((tameUniformizer K : K) * (x : K)) = 1
  rw [hz]
  exact hψ.integer z

def conductorResidueChar (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ) : AddChar 𝓀[K] ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (𝓂[K] : Ideal 𝒪[K]).toAddSubgroup
      (integerShiftCharacter K ψ).toAddMonoidHom (by
        intro x hx
        change integerShiftCharacter K ψ x = 1
        exact integerShiftCharacter_maximal K ψ hψ x hx))

theorem conductorResidueChar_apply (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (x : 𝒪[K]) :
    conductorResidueChar K ψ hψ (IsLocalRing.residue 𝒪[K] x) =
      ψ ((tameUniformizer K : K) * (x : K)) := rfl

theorem conductorResidueChar_nontrivial (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ) :
    conductorResidueChar K ψ hψ ≠ 1 := by
  intro he
  obtain ⟨x, hx⟩ := hψ.inverse_prime
  have h := congrArg (fun χ : AddChar 𝓀[K] ℂ => χ (IsLocalRing.residue 𝒪[K] x)) he
  rw [conductorResidueChar_apply, AddChar.one_apply] at h
  exact hx h

theorem conductorResidueChar_norm (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (hu : ∀ x : K, ‖ψ x‖ = 1) (z : 𝓀[K]) :
    ‖conductorResidueChar K ψ hψ z‖ = 1 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact hu _

theorem conductorResidueChar_quadratic (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (u : 𝒪[K]ˣ) (x : 𝒪[K]) :
    conductorResidueChar K ψ hψ
      ((localUnitResidue K u : 𝓀[K]) * (IsLocalRing.residue 𝒪[K] x) ^ 2) =
      ψ ((tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * (x : K) ^ 2) := by
  have h := conductorResidueChar_apply K ψ hψ ((u : 𝒪[K]) * x ^ 2)
  change conductorResidueChar K ψ hψ
    (IsLocalRing.residue 𝒪[K] (u : 𝒪[K]) * (IsLocalRing.residue 𝒪[K] x) ^ 2) =
      ψ ((tameUniformizer K : K) * ((u : 𝒪[K]) : K) * (x : K) ^ 2)
  simpa only [map_mul, map_pow,
    Subring.coe_mul, Subring.coe_pow, mul_assoc] using h

end

end ArtinMatthews.QuadraticWeil
