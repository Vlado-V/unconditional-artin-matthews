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


set_option backward.privateInPublic true
@[expose] public section

/-! The exact unit monomial of an active rotated Fourier row. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain VaryingKummerAnalytic AllowedGenerators StandardAdelic QuadraticWeil
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField Classical ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "res₀" => sourceKPLocalUnitResidue K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "A₀" => sourceReflectionTameActiveFourier K hζ S₀ P
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "D₀" => fun a : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal a)

local instance monomialResidueField : Field R :=
  let : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _

local instance monomialAdicRelation : ValuativeRel L := adicRelation K P.val
local instance monomialAdicLocalField : IsNonarchimedeanLocalField L := adicLocalField K P.val

def sourceReflectionTameValuationUnits : Subgroup Lˣ where
  carrier := {u | ν₀ (u : L) = 1}
  one_mem' := by change ν₀ (1 : L) = 1; exact map_one _
  mul_mem' {u v} hu hv := by
    change ν₀ (u : L) = 1 at hu
    change ν₀ (v : L) = 1 at hv
    change ν₀ ((u * v : Lˣ) : L) = 1
    rw [Units.val_mul, map_mul, hu, hv, mul_one]
  inv_mem' {u} hu := by
    change ν₀ (u : L) = 1 at hu
    change ν₀ ((u⁻¹ : Lˣ) : L) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

local notation "V" => sourceReflectionTameValuationUnits K S₀ P

def sourceReflectionTameUnitReduction : V →* Rˣ where
  toFun v := Units.mk0 (res₀ v.val v.property) (sourceKPLocalUnitResidue_ne_zero K P.val _ _)
  map_one' := by
    apply Units.ext
    let E := adicIntegerResidueEquiv K P.val
    change E.symm (IsLocalRing.residue 𝒪[L] 1) = 1
    rw [map_one, map_one]
  map_mul' u v := by
    apply Units.ext
    let E := adicIntegerResidueEquiv K P.val
    let uI : 𝒪[L] := ⟨u.val, (sourceKPLocalUnitInteger K P.val u.val u.property).property⟩
    let vI : 𝒪[L] := ⟨v.val, (sourceKPLocalUnitInteger K P.val v.val v.property).property⟩
    change E.symm (IsLocalRing.residue 𝒪[L] (uI * vI)) =
      E.symm (IsLocalRing.residue 𝒪[L] uI) * E.symm (IsLocalRing.residue 𝒪[L] vI)
    rw [map_mul, map_mul]

def sourceReflectionTameUnitCharacter : V →* ℂˣ :=
  (MulChar.equivToUnitHom χ₀).comp (sourceReflectionTameUnitReduction K S₀ P)

local notation "χ" => sourceReflectionTameUnitCharacter K hζ S₀ P

theorem sourceReflectionTameUnitCharacter_val (v : V) :
    (χ v : ℂ) = χ₀ (res₀ v.val v.property) :=
  MulChar.coe_equivToUnitHom _ _

theorem sourceReflectionTameUnitCharacter_pow_six (v : V) : χ v ^ (6 : ℕ) = 1 := by
  have hχ : χ₀ ^ (6 : ℕ) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, sourceJacquetActualCharacter_order]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, sourceReflectionTameUnitCharacter_val,
    ← MulChar.pow_apply' χ₀ (by decide : (6 : ℕ) ≠ 0), hχ]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr (sourceKPLocalUnitResidue_ne_zero K P.val _ _))

theorem sourceReflectionTameUnitCharacter_norm (v : V) : ‖(χ v : ℂ)‖ = 1 := by
  apply Complex.norm_eq_one_of_mem_rootsOfUnity (n := 6)
  rw [mem_rootsOfUnity]
  exact sourceReflectionTameUnitCharacter_pow_six K hζ S₀ P v

/-- The exponent at zero order differs from the source's (8-j) by six. -/
def sourceReflectionTameActiveExponent (j : Fin 6) (e : ℕ) : ℤ :=
  if e = 0 then 2 - j.val else 4 + 2 * e

variable (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

include hS in
private theorem active_fourier_unit (j : Fin 6) (v : V) :
    A₀ j (res₀ v.val v.property) = A₀ j 1 * ((χ v ^ (-((j.val + 2 : ℕ) : ℤ)) : ℂˣ) : ℂ) := by
  let x := res₀ v.val v.property
  have hx : x ≠ 0 := sourceKPLocalUnitResidue_ne_zero K P.val _ _
  rw [sourceReflectionTameActiveFourier_eq K hζ S₀ P hS,
    sourceReflectionTameActiveFourier_eq K hζ S₀ P hS]
  change (if _ then _ else _) = (if _ then _ else _) * _
  by_cases hj : j = 0
  · subst j
    simp [MulChar.inv_apply_eq_inv', MulChar.pow_apply' χ₀ (by decide : (2 : ℕ) ≠ 0),
      sourceReflectionTameUnitCharacter_val, zpow_neg]
  · rw [ite_eq_right hj, ite_eq_right hj]
    by_cases hj4 : j = 4
    · subst j
      have h6 : χ v ^ (-6 : ℤ) = 1 := by
        rw [zpow_neg, show (6 : ℤ) = ((6 : ℕ) : ℤ) from rfl, zpow_natCast,
          sourceReflectionTameUnitCharacter_pow_six, inv_one]
      rw [ite_eq_left rfl, ite_eq_left rfl]
      change (_ * (if x = 0 then _ else _)) = (_ * (if (1 : R) = 0 then _ else _)) *
        ((χ v ^ (-6 : ℤ) : ℂˣ) : ℂ)
      simp [hx, h6]
    · rw [ite_eq_right hj4, ite_eq_right hj4]
      have hn : j.val + 2 ≠ 0 := by omega
      simp only [MulChar.inv_apply_eq_inv', MulChar.pow_apply' χ₀ hn, MulChar.map_one, mul_one,
        zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
        sourceReflectionTameUnitCharacter_val]

theorem sourceReflectionTameRotatedActive_monomial (j : Fin 6) (e : ℕ) (v : V) :
    sourceReflectionTameRotatedActive K hζ S₀ P hS j e v.val =
      sourceReflectionTameRotatedActive K hζ S₀ P hS j e 1 *
        ((χ v ^ sourceReflectionTameActiveExponent j e : ℂˣ) : ℂ) := by
  let W₀ := sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
  have h1 : ν₀ ((1 : Lˣ) : L) = 1 := (1 : V).property
  have hres : res₀ 1 h1 = 1 := by
    let E := adicIntegerResidueEquiv K P.val
    change E.symm (IsLocalRing.residue 𝒪[L] 1) = 1
    rw [map_one, map_one]
  rw [sourceReflectionTameRotatedActive_eq K hζ S₀ P hS j e v.val v.property,
    sourceReflectionTameRotatedActive_eq K hζ S₀ P hS j e 1 h1, hres,
    MulChar.map_one, one_zpow, one_mul, mul_one,
    sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS (e : ℤ) v.val v.property,
    ← sourceReflectionTameUnitCharacter_val K hζ S₀ P v]
  change A₀ j (if e = 0 then res₀ v.val v.property else 0) *
      ((χ v : ℂ) ^ (4 : ℤ) * ((χ v : ℂ) ^ (2 * (e : ℤ)) * W₀ (D₀ (π₀ ^ (e : ℤ))))) =
    A₀ j (if e = 0 then 1 else 0) * W₀ (D₀ (π₀ ^ (e : ℤ))) *
      ((χ v ^ sourceReflectionTameActiveExponent j e : ℂˣ) : ℂ)
  by_cases he : e = 0
  · subst e
    simp only [ite_true, Nat.cast_zero, mul_zero, zpow_zero, one_mul, sourceReflectionTameActiveExponent,
      active_fourier_unit K hζ S₀ P hS, Units.val_zpow_eq_zpow_val]
    have hx : (χ v : ℂ) ≠ 0 := Units.ne_zero _
    have hb : 2 - (j.val : ℤ) = -((j.val + 2 : ℕ) : ℤ) + 4 := by push_cast; ring
    rw [hb, zpow_add₀ hx]
    ring
  · simp only [ite_eq_right he, sourceReflectionTameActiveExponent, Units.val_zpow_eq_zpow_val]
    rw [zpow_add₀ (Units.ne_zero (χ v))]
    ring

theorem sourceReflectionTameRotatedActive_one_zero (v : V) :
    sourceReflectionTameRotatedActive K hζ S₀ P hS 1 0 v.val =
      sourceReflectionTameRotatedActive K hζ S₀ P hS 1 0 1 * (χ v : ℂ) := by
  rw [sourceReflectionTameRotatedActive_monomial K hζ S₀ P hS]
  simp [sourceReflectionTameActiveExponent]

end
end ArtinMatthews
