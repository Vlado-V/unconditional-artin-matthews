module

public import ArtinMatthews.CompactFiniteAverage
public import ArtinMatthews.IntegerOpenSubgroup


set_option backward.privateInPublic true
@[expose] public section

/-! Evaluate the actual compact local quadratic integral by reduction to the
finite residue field, retaining its Haar-volume and residue-cardinality
constants. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss OAI.SevenEighths OAI.SevenEighths.FiniteFourier
open OAI.RepresentationTheory.Weil.Local
open scoped ValuativeRel Classical BigOperators

noncomputable section

variable (K : Type) [NormedField K] [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

theorem integer_quadratic_integral (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (hc : Continuous (fun x => ψ x)) (u : 𝒪[K]ˣ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    (∫ x in (integerOpenSubgroup K : Set K),
      ψ ((tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2) ∂μ) =
      ((μ.real (integerOpenSubgroup K : Set K) : ℂ) *
        ∑ z : 𝓀[K], conductorResidueChar K ψ hψ ((localUnitResidue K u : 𝓀[K]) * z ^ 2)) /
          Fintype.card 𝓀[K] := by
  apply compact_finite_integral μ (integerOpenSubgroup K) (integerOpenSubgroup_compact K)
    (integerReduction K) (integerReduction_surjective K)
  · exact hc.comp (by fun_prop)
  · intro x
    exact (conductorResidueChar_quadratic K ψ hψ u ⟨(x : K), x.property⟩).symm

theorem integer_quadratic_integral_phase (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
    (hc : Continuous (fun x => ψ x)) (u : 𝒪[K]ˣ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    FunctionsMetaplectic.Construction.phase
      (∫ x in (integerOpenSubgroup K : Set K),
        ψ ((tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2) ∂μ) =
      FunctionsMetaplectic.Construction.phase
        (∑ z : 𝓀[K], conductorResidueChar K ψ hψ ((localUnitResidue K u : 𝓀[K]) * z ^ 2)) := by
  apply compact_finite_integral_phase μ (integerOpenSubgroup K) (integerOpenSubgroup_compact K)
    (integerReduction K) (integerReduction_surjective K)
  · exact hc.comp (by fun_prop)
  · intro x
    exact (conductorResidueChar_quadratic K ψ hψ u ⟨(x : K), x.property⟩).symm

theorem integer_quadratic_integral_phase_eq_index
    (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ) (hc : Continuous (fun x => ψ x))
    (hF : ringChar 𝓀[K] ≠ 2) (u : 𝒪[K]ˣ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    FunctionsMetaplectic.Construction.phase
      (∫ x in (integerOpenSubgroup K : Set K),
        ψ ((tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2) ∂μ) =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) *
        residueIndex 𝓀[K] (conductorResidueChar K ψ hψ) := by
  rw [integer_quadratic_integral_phase K ψ hψ hc u μ,
    square_sum_scaled hF _ (conductorResidueChar_nontrivial K ψ hψ) (localUnitResidue K u).ne_zero]
  have hχ : ‖residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K])‖ = 1 := by
    change ‖(quadraticChar 𝓀[K] (localUnitResidue K u : 𝓀[K]) : ℂ)‖ = 1
    rcases quadraticChar_dichotomy (localUnitResidue K u).ne_zero with h | h <;> rw [h] <;> norm_num
  have hg := primitive_gaussSum_norm (residueCharacter 𝓀[K])
    (primitiveOnIdeals_of_field _ (residueCharacter_nontrivial hF))
    (conductorResidueChar K ψ hψ)
    (AddChar.IsPrimitive.of_ne_one (conductorResidueChar_nontrivial K ψ hψ))
  rw [FunctionsMetaplectic.Construction.phase, norm_mul, hχ, one_mul, hg]
  exact mul_div_assoc _ _ _

end

end ArtinMatthews.QuadraticWeil
