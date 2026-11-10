module

public import ArtinMatthews.IntegerConductor
public import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic
public import ArtinMatthews.AnalyticTameBase
public import ArtinMatthews.IntegerConductorDual
public import ArtinMatthews.NormedUltrametricTopology
public import ArtinMatthews.TameParityDecomposition
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.Local.GaussianSquareClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Identify the actual analytic normalized Weil index with the residue
Gauss section at every tame valuation.  The extension from valuations zero
and one uses the proved analytic change of variables by a square. -/

namespace ArtinMatthews.QuadraticWeil

open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open ArtinMatthews.QuadraticGauss
open OAI.RepresentationTheory.Weil.Local
open scoped ValuativeRel Classical

noncomputable section

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K] [CharZero K]
  [MeasurableSpace K] [BorelSpace K]

local instance : Fintype 𝓀[K] := Fintype.ofFinite _

variable (hnorm : ∀ x : K, x ∈ (ValuativeRel.valuation K).integer ↔ ‖x‖ ≤ 1)
  (ψ : AddChar K ℂ) (hψ : ConductorZero K ψ)
  (hu : ∀ x : K, ‖ψ x‖ = 1) (hc : Continuous (fun x => ψ x))
  (h2 : ValuativeRel.valuation K (2 : K) = 1)

include hnorm hψ hu hc h2 in
theorem analyticIndex_eq_localTameGaussSection (x : Kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex K ψ (2 * (x : K)) =
      localTameGaussSection K (conductorResidueChar K ψ hψ) x := by
  let : NonarchimedeanAddGroup K := ultrametric_nonarchimedean K
  let m := valuationMap K (Additive.ofMul x)
  let u := tameUnitFactor K x
  let b := tameUniformizer K ^ (m / 2)
  have hd := tameParityDecomposition K x
  change x = (integerUnitsToFieldUnits K u * tameUniformizer K ^ (m % 2)) * b ^ 2 at hd
  by_cases hm : Even m
  · have hr : m % 2 = 0 := Int.even_iff.mp hm
    have hx : x = integerUnitsToFieldUnits K u * b ^ 2 := by
      simpa only [hr, zpow_zero, mul_one] using hd
    have hcoeff : (2 : K) * (x : K) =
        (2 * (integerUnitsToFieldUnits K u : K)) * (b : K) ^ 2 := by
      calc
        _ = 2 * ((integerUnitsToFieldUnits K u * b ^ 2 : Kˣ) : K) :=
          congrArg (fun a : Kˣ => (2 : K) * (a : K)) hx
        _ = _ := by rw [Units.val_mul, Units.val_pow_eq_pow_val]; ring
    rw [hcoeff, GaussianSquareClasses.Construction.nonarchimedean_gaussianIndex_square_mul
      (nontrivialNorm_not_discrete K) ψ hu hc (conductorZero_nontrivial K ψ hψ) _
      (mul_ne_zero (by norm_num) (integerUnitsToFieldUnits K u).ne_zero) b,
      analyticIndex_unit K hnorm ψ hψ hu hc h2 u]
    exact (tameSection_even (conductorResidueChar K ψ hψ) hm (tameResidueUnit K x)).symm
  · have hr : m % 2 = 1 := Int.not_even_iff.mp hm
    have hx : x = (integerUnitsToFieldUnits K u * tameUniformizer K) * b ^ 2 := by
      simpa only [hr, zpow_one] using hd
    have hcoeff : (2 : K) * (x : K) =
        (2 * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K)) * (b : K) ^ 2 := by
      calc
        _ = 2 * (((integerUnitsToFieldUnits K u * tameUniformizer K) * b ^ 2 : Kˣ) : K) :=
          congrArg (fun a : Kˣ => (2 : K) * (a : K)) hx
        _ = _ := by rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val]; ring
    have hbase : (2 : K) * (tameUniformizer K : K) * (integerUnitsToFieldUnits K u : K) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (tameUniformizer K).ne_zero)
        (integerUnitsToFieldUnits K u).ne_zero
    rw [hcoeff, GaussianSquareClasses.Construction.nonarchimedean_gaussianIndex_square_mul
      (nontrivialNorm_not_discrete K) ψ hu hc (conductorZero_nontrivial K ψ hψ) _ hbase b,
      analyticIndex_primeUnit K hnorm ψ hψ hu hc h2 u]
    change residueCharacter 𝓀[K] (localUnitResidue K u : 𝓀[K]) *
        residueIndex 𝓀[K] (conductorResidueChar K ψ hψ) =
      tameSection (conductorResidueChar K ψ hψ) m (tameResidueUnit K x)
    rw [tameSection_odd _ hm]
    exact mul_comm _ _

include hnorm hψ hu hc h2 in
theorem normalizedAnalyticWeil_eq_localTameGaussSection (x : Kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex K ψ (2 * (x : K)) /
        FunctionsMetaplectic.Construction.gaussianIndex K ψ 2 =
      localTameGaussSection K (conductorResidueChar K ψ hψ) x := by
  rw [analyticIndex_two K hnorm ψ hψ hu hc h2, div_one]
  exact analyticIndex_eq_localTameGaussSection K hnorm ψ hψ hu hc h2 x

end

end ArtinMatthews.QuadraticWeil
