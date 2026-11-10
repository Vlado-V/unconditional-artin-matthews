module

public import ArtinMatthews.IntegerConductor
public import ArtinMatthews.IntegerOpenSubgroup
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import ArtinMatthews.GaussianIntegerDomain
public import ArtinMatthews.IntegerQuadraticHaar
public import ArtinMatthews.NormedUltrametricTopology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import OAI.RepresentationTheory.Weil.Local.Gaussian
public import OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Actual analytic Gaussian evaluations in the two valuation parity base
cases.  The factor two converts OAI's form `c*x²/2` to the form `a*x²`. -/

namespace ArtinMatthews.QuadraticWeil

open MeasureTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.Local
open scoped ValuativeRel Classical BigOperators

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
  [MeasurableSpace K] [BorelSpace K]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

omit [IsUltrametricDist K] [IsNonarchimedeanLocalField K] [CharZero K]
  [MeasurableSpace K] [BorelSpace K] in
theorem integerUnit_valuation (u : 𝒪[K]ˣ) :
    ValuativeRel.valuation K (integerUnitsToFieldUnits K u : K) = 1 := by
  change ValuativeRel.valuation K (((u : 𝒪[K]) : K)) = 1
  exact Valuation.Integers.valuation_unit (Valuation.integer.integers (ValuativeRel.valuation K)) u

variable (hnorm : ∀ x : K, x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1)
  (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
  (hu : ∀ x : K, ‖ψ x‖ = 1) (hc : Continuous (fun x => ψ x))
  (h2 : ValuativeRel.valuation K (2 : K) = 1)

include hnorm hψ hu hc h2 in
theorem analyticGaussian_unit (u : 𝒪[K]ˣ) :
    FunctionsMetaplectic.Construction.gaussianIntegral K ψ
      (2 * (integerUnitsToFieldUnits K u : K)) =
      ((Measure.addHaar : Measure K).real (integerOpenSubgroup K : Set K) : ℂ) := by
  have hcoeff : (2 : K) * (integerUnitsToFieldUnits K u : K) ≠ 0 :=
    mul_ne_zero (by norm_num) (integerUnitsToFieldUnits K u).ne_zero
  have hi : ((2 : K) * (integerUnitsToFieldUnits K u : K))⁻¹ ∈
      (ValuativeRel.valuation K).integer := by
    change ValuativeRel.valuation K _ ≤ 1
    rw [map_inv₀, map_mul, h2, integerUnit_valuation, one_mul, inv_one]
  rw [gaussianIntegral_eq_integer_integral K hnorm (nontrivialNorm_not_discrete K)
    ψ hψ hu hc h2 _ hcoeff hi]
  calc
    _ = ∫ _ in (integerOpenSubgroup K : Set K), (1 : ℂ)
        ∂(Measure.addHaar : Measure K) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (integerOpenSubgroup K).isOpen.measurableSet] with x hx
      have heq : (2 : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2 / 2 =
          (integerUnitsToFieldUnits K u : K) * x ^ 2 := by ring
      rw [heq]
      exact hψ.integer ((u : 𝒪[K]) * ⟨x, hx⟩ ^ 2)
    _ = _ := by simp only [integral_const, Complex.real_smul, mul_one,
      Measure.real, Measure.restrict_apply_univ]

include hnorm hψ hu hc h2 in
theorem analyticIndex_unit (u : 𝒪[K]ˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex K ψ
      (2 * (integerUnitsToFieldUnits K u : K)) = 1 := by
  rw [FunctionsMetaplectic.Construction.gaussianIndex,
    analyticGaussian_unit K hnorm ψ hψ hu hc h2 u]
  exact Gaussian.Construction.phase_positive_real _
    (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos
      Measure.addHaar (integerOpenSubgroup K) (integerOpenSubgroup_compact K))

include hnorm hψ hu hc h2 in
theorem analyticIndex_two : FunctionsMetaplectic.Construction.gaussianIndex K ψ 2 = 1 := by
  simpa only [map_one, Units.val_one, mul_one] using
    analyticIndex_unit K hnorm ψ hψ hu hc h2 1

omit [IsUltrametricDist K] [CharZero K] [MeasurableSpace K] [BorelSpace K] in
include h2 in
theorem inverse_twoPrimeUnit_integral (u : 𝒪[K]ˣ) :
    ((2 : K) * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K))⁻¹ ∈
      (ValuativeRel.valuation K).integer := by
  have hp : ValuativeRel.valuation K (tameUniformizer K : K)⁻¹ ≤ 1 := by
    change ValuativeRel.valuation K (((chosenIntegerRingUniformizer K : K)⁻¹)⁻¹) ≤ 1
    rw [inv_inv]
    exact (chosenIntegerRingUniformizer K).property
  change ValuativeRel.valuation K _ ≤ 1
  simpa only [map_inv₀, map_mul, h2, integerUnit_valuation, one_mul, mul_one] using hp

include hnorm hψ hu hc h2 in
theorem analyticGaussian_primeUnit (u : 𝒪[K]ˣ) :
    FunctionsMetaplectic.Construction.gaussianIntegral K ψ
      (2 * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K)) =
      (((Measure.addHaar : Measure K).real (integerOpenSubgroup K : Set K) : ℂ) *
        ∑ z : 𝓀[K], conductorResidueChar K ψ hψ ((localUnitResidue K u : 𝓀[K]) * z ^ 2)) /
          Fintype.card 𝓀[K] := by
  have hcoeff : (2 : K) * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (tameUniformizer K).ne_zero)
      (integerUnitsToFieldUnits K u).ne_zero
  rw [gaussianIntegral_eq_integer_integral K hnorm (nontrivialNorm_not_discrete K)
    ψ hψ hu hc h2 _ hcoeff (inverse_twoPrimeUnit_integral K h2 u)]
  have heq (x : K) : (2 : K) * (tameUniformizer K : K) *
      (integerUnitsToFieldUnits K u : K) * x ^ 2 / 2 =
      (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2 := by ring
  simp only [heq]
  exact integer_quadratic_integral K ψ hψ hc u Measure.addHaar

include hnorm hψ hu hc h2 in
theorem analyticIndex_primeUnit (u : 𝒪[K]ˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex K ψ
      (2 * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K)) =
      residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) *
        residueIndex 𝓀[K] (conductorResidueChar K ψ hψ) := by
  have hcoeff : (2 : K) * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (tameUniformizer K).ne_zero)
      (integerUnitsToFieldUnits K u).ne_zero
  rw [FunctionsMetaplectic.Construction.gaussianIndex,
    gaussianIntegral_eq_integer_integral K hnorm (nontrivialNorm_not_discrete K)
      ψ hψ hu hc h2 _ hcoeff (inverse_twoPrimeUnit_integral K h2 u)]
  have heq (x : K) : (2 : K) * (tameUniformizer K : K) *
      (integerUnitsToFieldUnits K u : K) * x ^ 2 / 2 =
      (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) * x ^ 2 := by ring
  simp only [heq]
  exact integer_quadratic_integral_phase_eq_index K ψ hψ hc
    (tameResidue_char_ne_two K h2) u Measure.addHaar

end

end ArtinMatthews.QuadraticWeil
