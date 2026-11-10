module

public import ArtinMatthews.IntegerOpenSubgroup
public import ArtinMatthews.IntegerConductor
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import ArtinMatthews.CompactFiniteAverage
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.DirichletL.FiniteFourier


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
