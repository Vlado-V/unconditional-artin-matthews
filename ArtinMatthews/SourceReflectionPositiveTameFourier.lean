module

public import ArtinMatthews.SourceReflectionTameRotation
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

/-! The positive finite twist uses the same nonzero lifts as the
rotation. The zero residue is lifted by zero. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic StandardAdelic QuadraticWeil
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField Classical BigOperators ValuativeRel

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "I" => sourceJacquetIntegers K P.val
local notation "red" => sourceJacquetReduction K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "φ₀" => sourceJacquetActualPositivePhase K hζ S₀ P
local notation "C₀" => sourceReflectionTameFourierCoefficient K hζ S₀ P

local instance positiveResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _

local instance positiveResidueFinite : Finite R :=
  Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot

local instance positiveResidueFintype : Fintype R := Fintype.ofFinite _

local instance positiveAdicRelation : ValuativeRel L := adicRelation K P.val

local instance positiveAdicLocalField : IsNonarchimedeanLocalField L := adicLocalField K P.val

def sourceReflectionPositiveResidueLift (a : R) : I :=
  if ha : a = 0 then 0 else
    sourceKPLocalUnitInteger K P.val (sourceReflectionTameUnitLift K S₀ P (Units.mk0 a ha))
      (sourceReflectionTameUnitLift_valuation K S₀ P (Units.mk0 a ha))

theorem sourceReflectionPositiveResidueLift_zero :
    sourceReflectionPositiveResidueLift K S₀ P 0 = 0 := by
  rw [sourceReflectionPositiveResidueLift, dite_eq_left rfl]

theorem sourceReflectionPositiveResidueLift_reduce (a : R) :
    red (sourceReflectionPositiveResidueLift K S₀ P a) = a := by
  by_cases ha : a = 0
  · rw [ha, sourceReflectionPositiveResidueLift_zero, map_zero]
  · rw [sourceReflectionPositiveResidueLift, dite_eq_right ha]
    exact sourceReflectionTameUnitLift_residue K S₀ P (Units.mk0 a ha)

def sourceReflectionPositiveLocalTranslation (a : R) : L :=
  (π₀ : L)⁻¹ * (sourceReflectionPositiveResidueLift K S₀ P a : L)

theorem sourceReflectionPositiveLocalTranslation_zero :
    sourceReflectionPositiveLocalTranslation K hζ S₀ P 0 = 0 := by
  rw [sourceReflectionPositiveLocalTranslation, sourceReflectionPositiveResidueLift_zero]
  exact mul_zero _

theorem sourceReflectionPositiveLocalPhase
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (x : I) (a : R) :
    ψ₀ ((x : L) * sourceReflectionPositiveLocalTranslation K hζ S₀ P a) =
      φ₀ (a * red x) := by
  let A : 𝒪[L] := ⟨(sourceReflectionPositiveResidueLift K S₀ P a : L),
    (sourceReflectionPositiveResidueLift K S₀ P a).property⟩
  let X : 𝒪[L] := ⟨(x : L), x.property⟩
  let y : I := ⟨(A*X : 𝒪[L]), (A*X).property⟩
  have hr : red y = a * red x := by
    rw [← sourceReflectionPositiveResidueLift_reduce K S₀ P a]
    let E := adicIntegerResidueEquiv K P.val
    change E.symm (IsLocalRing.residue 𝒪[L] (A*X)) =
      E.symm (IsLocalRing.residue 𝒪[L] A) * E.symm (IsLocalRing.residue 𝒪[L] X)
    rw [map_mul, map_mul]
  rw [← hr, sourceReflectionTamePositivePhase_reduction K hζ S₀ P hS y]
  congr 1
  change (x : L) * ((π₀ : L)⁻¹ * (A : L)) = (π₀ : L)⁻¹ * ((A : L) * (X : L))
  change (x : L) * ((π₀ : L)⁻¹ * (A : L)) = (π₀ : L)⁻¹ * ((A : L) * (x : L))
  ac_rfl

theorem sourceReflectionPositiveLocalFourier
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀) (j : Fin 6) (x : I) :
    (∑ a : R, C₀ j a * ψ₀ ((x : L) * sourceReflectionPositiveLocalTranslation K hζ S₀ P a)) =
      (reflectionPrimeCharacters K hζ S₀ P ^ j.val : MulChar R ℂ) (red x) := by
  simp_rw [sourceReflectionPositiveLocalPhase K hζ S₀ P hS x]
  exact sourceReflectionTameFourier_inversion K hζ S₀ P hS j (red x)

end
end ArtinMatthews
