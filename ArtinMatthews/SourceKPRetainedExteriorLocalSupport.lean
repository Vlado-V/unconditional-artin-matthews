module

public import ArtinMatthews.SourceKPExteriorWhittakerPhase
public import ArtinMatthews.SourceFrequencyUnitPart
public import ArtinMatthews.SourceKPExteriorWhittakerAllowed
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceReflectionTameRotationSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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


set_option backward.privateInPublic true
@[expose] public section

/-! The spherical exterior coefficient uses the actual principal-ideal
orders of arbitrary rational frequencies. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "ν" => sourceKPFiniteVal K

def sourceKPRetainedRationalLocalUnit (P : Pr) : Kˣ →* (P.adicCompletion K)ˣ :=
  Units.map (algebraMap K (P.adicCompletion K)).toMonoidHom

local notation "loc" => sourceKPRetainedRationalLocalUnit K

theorem sourceKPRetainedExteriorOrder_local (P : Pr) (m : Kˣ) :
    sourceKPValuationOrder (ν P) (loc P m) = exteriorPrincipalValuation P m := by
  have hv : P.valuation K (m:K) ≠ 0 := (Valuation.ne_zero_iff _).mpr m.ne_zero
  apply (sourceKPValuationOrder_eq (ν P) (loc P m) _).mpr
  rw [sourceExteriorPrincipalValuation_eq_neg_log, neg_neg, WithZero.exp_log hv]
  change Valued.v (((m:K):P.adicCompletion K)) = P.valuation K (m:K)
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem sourceKPRetainedRationalLocalUnit_valuation (P : Pr) (m : Kˣ) :
    ν P (loc P m : P.adicCompletion K) = WithZero.exp (-exteriorPrincipalValuation P m) := by
  rw [sourceKPValuationOrder_spec, sourceKPRetainedExteriorOrder_local]

theorem sourceKPRetainedRationalLocalUnit_valuation_one (P : Pr) (m : Kˣ)
    (hm : P.valuation K (m:K) = 1) : ν P (loc P m : P.adicCompletion K) = 1 := by
  change Valued.v (((m:K):P.adicCompletion K)) = 1
  rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem sourceKPRetainedExteriorLocal_one_of_order_zero
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (P : SourceExteriorPrime K S₀) (m : Kˣ) (hm : exteriorPrincipalValuation P.val m = 0) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS m = 1 := by
  have hv : ν P.val (loc P.val m : P.val.adicCompletion K) = 1 := by
    rw [sourceKPRetainedRationalLocalUnit_valuation, hm, neg_zero, WithZero.exp_zero]
  have h := sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS 0 (loc P.val m) hv
  change sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
    (sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal (loc P.val m))) = 1
  rw [zpow_zero, one_mul, mul_zero, zpow_zero, one_mul] at h
  have hD : sourceGL2Diagonal (1 : (P.val.adicCompletion K)ˣ) = 1 :=
    (sourceGL2DiagonalHom (P.val.adicCompletion K)).map_one
  rwa [hD, sourceFiniteKP2ProjectiveLift_one, sourceKPTameCyclicWhittakerValue_one] at h

theorem sourceKPRetainedExteriorLocal_zero_of_bad_order
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (P : SourceExteriorPrime K S₀) (m : Kˣ)
    (hm : exteriorPrincipalValuation P.val m < 0 ∨ exteriorPrincipalValuation P.val m % 3 = 2) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS m = 0 := by
  let a := loc P.val m
  let v := ν P.val
  let j := sourceKPValuationOrder v a
  let π := sourceKPTameExteriorUniformizer K hζ S₀ P
  let u := sourceKPUnitPart v π a
  let W := sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
  let D := sourceFiniteKP2ProjectiveLift K hζ P.val
  have hj : j = exteriorPrincipalValuation P.val m := sourceKPRetainedExteriorOrder_local K P.val m
  change W (D (sourceGL2Diagonal a)) = 0
  by_cases hn : j < 0
  · exact sourceKPTameCyclicWhittakerValue_diagonal_order_negative K hζ S₀ P hS a hn
  · have hmod : j % 3 = 2 := by
      rw [← hj] at hm
      exact hm.resolve_left hn
    have hnonneg : 0 ≤ j := le_of_not_gt hn
    have hcast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hnonneg
    have he : ((3*(j.toNat / 3)+2:ℕ):ℤ) = j := by omega
    have hu : v (u : P.val.adicCompletion K) = 1 :=
      sourceKPUnitPart_valuation v π (sourceKPTameExteriorUniformizer_valuation K hζ S₀ P) a
    have hfac : π^j*u = a := sourceKPUnitPart_factor v π a
    have hz := sourceKPTameCyclicWhittakerValue_diagonal_three_add_two K hζ S₀ P hS (j.toNat / 3)
    rw [he] at hz
    change W (D (sourceGL2Diagonal (π^j))) = 0 at hz
    have hunit := sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS j u hu
    change W (D (sourceGL2Diagonal (π^j*u))) = _ * W (D (sourceGL2Diagonal (π^j))) at hunit
    rw [← hfac, hunit, hz, mul_zero]

theorem sourceKPRetainedExteriorLocal_mul_sixth
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    (P : SourceExteriorPrime K S₀) (m r : Kˣ) (hr : P.val.valuation K (r:K) = 1) :
    sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (m*r^6) =
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS m := by
  let W := sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
  let D := sourceFiniteKP2ProjectiveLift K hζ P.val
  change W (D (sourceGL2Diagonal (loc P.val (m*r^6)))) = W (D (sourceGL2Diagonal (loc P.val m)))
  rw [map_mul, map_pow]
  exact sourceKPTameCyclicWhittakerValue_diagonal_mul_sixth K hζ S₀ hS P _ _
    (sourceKPRetainedRationalLocalUnit_valuation_one K P.val r hr)

end
end ArtinMatthews
