module

public import ArtinMatthews.StandardLocalConductor
public import ArtinMatthews.ArtinRayCompletedPower
public import ArtinMatthews.HenselPowerUnits
public import ArtinMatthews.SourceKPJacquetTinyUnits
public import ArtinMatthews.StandardLocalBall
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlaceCompletionInstances
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! A sufficiently small unit has a cube root in any prescribed
principal valuation ball. The Hensel construction retains the bound
on the root's difference from one. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain SourcePhysical
open scoped NumberField SourcePhysical

noncomputable section

variable (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "O" => P.adicCompletionIntegers K
local notation "B" => sourceLocalBall K P
local notation "ν" => sourceLocalValuation K P

theorem sourceKPRetained_close_cube (n : ℤ) (hn : n < 0) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ t : Lˣ, ((t : L)-1) ∈ B (-(M:ℤ)) →
      ∃ w : Lˣ, w^3 = t ∧ ((w : L)-1) ∈ B n := by
  let c := sourceLocalBallScale K P n
  have hc : c ≠ 0 := sourceLocalBallScale_ne_zero K P n
  have h3 : (3 : L) ≠ 0 := by norm_num
  obtain ⟨M,hM,hsub⟩ := sourceKPJacquet_scaled_integer_contains_ball K P
    ((3:L)^2*c) (mul_ne_zero (pow_ne_zero _ h3) hc)
  refine ⟨M,hM,fun t ht => ?_⟩
  obtain ⟨x,hx,hxe⟩ := hsub ht
  let s := c*x
  have hs : s ∈ B n := by
    rw [sourceLocalBall_eq_scaled_zero]
    exact ⟨x,(sourceLocalBall_zero K P).symm ▸ hx,rfl⟩
  have hsmall : ν s < 1 := (show ν s ≤ WithZero.exp n from hs).trans_lt (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr hn)
  let a : O := ⟨s,(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mpr hsmall.le⟩
  have ha : a ∈ IsLocalRing.maximalIdeal O :=
    (Valuation.mem_maximalIdeal_iff L Valued.v).mpr hsmall
  let : HenselianLocalRing O := VaryingKummerAnalytic.ArtinRay.completedIntegers_henselianLocalRing P
  obtain ⟨r,hr⟩ := HenselPower.exists_unit_root_powerPolynomial (R := O) 3 (by decide) ha
  let v : O := ((r:O)+(3:O)*a) * ((r⁻¹ : Oˣ):O)
  have hrEq : ((r:O)+(3:O)*a)^3 = (1+(3:O)^2*a)*(r:O)^3 := by
    simpa only [Nat.cast_ofNat] using HenselPower.power_eq_of_isRoot 3 (by decide) a r hr
  have hvpow : v^3 = 1+(3:O)^2*a := by
    dsimp only [v]
    rw [mul_pow, hrEq, mul_assoc, ← mul_pow]
    simp
  let w₀ := algebraMap O L v
  have hw₀ : w₀^3 = (t:L) := calc
    _ = algebraMap O L (v^3) := (map_pow _ _ _).symm
    _ = algebraMap O L (1+(3:O)^2*a) := congrArg (algebraMap O L) hvpow
    _ = _ := by
      simp only [map_add, map_one, map_mul, map_pow, map_ofNat]
      change 1+(3:L)^2*(c*x) = (t:L)
      change (3:L)^2*c*x = (t:L)-1 at hxe
      rw [← mul_assoc, hxe]
      ring
  have hwne : w₀ ≠ 0 := fun hz => t.ne_zero (by simp [hz] at hw₀; exact hw₀.symm)
  let w : Lˣ := Units.mk0 w₀ hwne
  refine ⟨w,Units.ext ?_,?_⟩
  · change w₀^3 = (t:L)
    exact hw₀
  have hminus : v-1 = (3:O)*a*((r⁻¹ : Oˣ):O) := by
    dsimp only [v]
    rw [add_mul, Units.mul_inv, add_sub_cancel_left]
  have he : w₀-1 = (3:L)*s*algebraMap O L ((r⁻¹ : Oˣ):O) := by
    change algebraMap O L v - 1 = _
    rw [← map_one (algebraMap O L), ← map_sub, hminus, map_mul, map_mul, map_ofNat]
    rfl
  have hv3 : ν (3:L) ≤ 1 := by
    simpa only [map_ofNat] using
      (show ν (algebraMap O L (3:O)) ≤ 1 from (3:O).property)
  have hvri : ν (algebraMap O L ((r⁻¹ : Oˣ):O)) ≤ 1 :=
    ((r⁻¹ : Oˣ):O).property
  change ν (w₀-1) ≤ WithZero.exp n
  rw [he, map_mul, map_mul]
  calc
    _ ≤ 1 * ν s * 1 := mul_le_mul' (mul_le_mul' hv3 le_rfl) hvri
    _ = ν s := by rw [one_mul, mul_one]
    _ ≤ _ := hs

end
end ArtinMatthews
