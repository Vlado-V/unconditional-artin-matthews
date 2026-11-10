module

public import ArtinMatthews.SourceReflectionTameRotation
public import ArtinMatthews.SourceReflectionTameNormalization
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rotated terms vanish at negative order of their
rescaled diagonal, by the measured tame Jacquet support theorem. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "D₀" => fun a : Lˣ => l₀ (sourceGL2Diagonal a)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "N₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P
local notation "u₀" => sourceReflectionTameUnitLift K S₀ P

local instance supportResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance supportResidueFinite : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance supportResidueFintype : Fintype R := Fintype.ofFinite _

theorem sourceKPTameCyclicWhittakerValue_diagonal_order_negative (a : Lˣ)
    (ha : sourceKPValuationOrder ν₀ a < 0) :
    W₀ (D₀ a) = 0 := by
  let e := sourceKPValuationOrder ν₀ a
  let v := sourceKPUnitPart ν₀ π₀ a
  have hv : ν₀ (v : L) = 1 := sourceKPUnitPart_valuation ν₀ π₀ hπ₀ a
  have he : a = π₀ ^ e * v := (sourceKPUnitPart_factor ν₀ π₀ a).symm
  rw [he, sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS e v hv,
    sourceKPTameCyclicWhittakerValue_diagonal_negative K hζ S₀ P hS e ha, mul_zero]

theorem sourceReflectionTameRotatedActive_zero_of_negative_order (j : Fin 6) (t d : Lˣ)
    (hd : ν₀ (d : L) = 1) (he : sourceKPValuationOrder ν₀ (t * (π₀ * d) ^ (2 : ℤ)) < 0) :
    (∑ h : Rˣ, C₀ j h * W₀ (D₀ t * w₀ * N₀ ((π₀ ^ (-1 : ℤ) * u₀ h : Lˣ) : L))) = 0 := by
  apply Finset.sum_eq_zero
  intro h _
  rw [sourceKPTameCyclicWhittakerValue_weyl_normalized K hζ S₀ P hS t d (u₀ h) hd
    (sourceReflectionTameUnitLift_valuation K S₀ P h),
    sourceKPTameCyclicWhittakerValue_diagonal_order_negative K hζ S₀ P hS _ he]
  simp only [mul_zero]

theorem sourceReflectionTameRotatedInactive_zero_of_negative_order (j : Fin 6) (t b : Lˣ)
    (hb : ν₀ (b : L) = 1) (he : sourceKPValuationOrder ν₀ (t * b ^ (2 : ℤ)) < 0) :
    C₀ j 0 * W₀ (D₀ t * w₀ * N₀ 0) = 0 := by
  rw [sourceReflectionTameRotatedInactive_normalized K hζ S₀ P hS j t b hb,
    sourceKPTameCyclicWhittakerValue_diagonal_order_negative K hζ S₀ P hS _ he]
  simp only [mul_zero]

end
end ArtinMatthews
