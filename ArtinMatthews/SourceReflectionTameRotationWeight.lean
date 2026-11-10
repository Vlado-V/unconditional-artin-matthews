module

public import ArtinMatthews.SourceReflectionTameRotation
public import ArtinMatthews.SourceReflectionFrozenLocal
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Exact magnitudes of the actual active Fourier row. A positive
frequency order forces the Ramanujan branch and gives its full
(1-q^{-1}) factor in front of the frozen-prime weight. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open SourceEulerAssembly
open scoped NumberField Classical MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "R" => (𝓞 K) ⧸ P.val.asIdeal
local notation "L" => P.val.adicCompletion K
local notation "ν₀" => sourceKPFiniteVal K P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "res₀" => sourceKPLocalUnitResidue K P.val
local notation "χ₀" => reflectionPrimeCharacters K hζ S₀ P
local notation "Γ₀" => sourceJacquetActualGauss K hζ S₀ P
local notation "D₀" => fun a : Lˣ => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Diagonal a)
local notation "W₀" => sourceKPTameCyclicWhittakerValue K hζ S₀ P hS
local notation "A₀" => sourceReflectionTameActiveFourier K hζ S₀ P
local notation "q" => (Ideal.absNorm P.val.asIdeal : ℝ)

local instance weightResidueField : Field R :=
  letI : P.val.asIdeal.IsMaximal := P.val.isMaximal
  Ideal.Quotient.field _
local instance weightResidueFinite : Finite R := Ring.HasFiniteQuotients.finiteQuotient P.val.ne_bot
local instance weightResidueFintype : Fintype R := Fintype.ofFinite _

private theorem residue_norm_ge_one : 1 ≤ q := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.val.ne_bot)

private theorem character_norm_at_unit (χ : MulChar R ℂ) (x : R) (hx : x ≠ 0) : ‖χ x‖ = 1 :=
  Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity (Units.mk0 x hx))

private theorem scale_norm (s : ℝ) : ‖sourceJacquetScale q s‖ = q ^ s := by
  rw [sourceJacquetScale, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

private theorem diagonal_norm (e : ℕ) (v : Lˣ) (hv : ν₀ (v : L) = 1) :
    ‖W₀ (D₀ (π₀ ^ (e : ℤ) * v))‖ =
      if e % 3 = 0 then q ^ (-((e / 3 : ℕ) : ℝ))
      else if e % 3 = 1 then q ^ (-((e / 3 : ℕ) : ℝ) - 1 / 2)
      else 0 := by
  rw [sourceKPTameCyclicWhittakerValue_diagonal_unit K hζ S₀ P hS (e : ℤ) v hv,
    norm_mul, norm_zpow, character_norm_at_unit K S₀ P χ₀ _ (sourceKPLocalUnitResidue_ne_zero K P.val v hv),
    one_zpow, one_mul]
  let k := e / 3
  by_cases h0 : e % 3 = 0
  · have he : e = 3 * k := by dsimp only [k]; omega
    rw [ite_eq_left h0]
    change ‖W₀ (D₀ (π₀ ^ (e : ℤ)))‖ = q ^ (-(k : ℝ))
    rw [he, sourceKPTameCyclicWhittakerValue_diagonal_three, scale_norm K S₀ P]
  · rw [ite_eq_right h0]
    by_cases h1 : e % 3 = 1
    · have he : e = 3 * k + 1 := by dsimp only [k]; omega
      rw [ite_eq_left h1]
      change ‖W₀ (D₀ (π₀ ^ (e : ℤ)))‖ = q ^ (-(k : ℝ) - 1 / 2)
      rw [he, sourceKPTameCyclicWhittakerValue_diagonal_three_add_one, norm_mul, scale_norm K S₀ P,
        sourceJacquetActualGauss_norm K hζ S₀ P hS 2 (by decide), mul_one]
    · have he : e = 3 * k + 2 := by dsimp only [k]; omega
      rw [ite_eq_right h1, he, sourceKPTameCyclicWhittakerValue_diagonal_three_add_two, norm_zero]

include hS in
private theorem active_fourier_norm (j : Fin 6) (x : R) :
    ‖A₀ j x‖ =
      if j = 4 then (if x = 0 then q - 1 else 1) / Real.sqrt q
      else if x = 0 then 0 else if j = 0 then (Real.sqrt q)⁻¹ else 1 := by
  rw [sourceReflectionTameActiveFourier_eq K hζ S₀ P hS]
  by_cases hj4 : j = 4
  · subst j
    simp only [ite_eq_right (by decide : (4 : Fin 6) ≠ 0), eq_self, ite_true,
      norm_mul, norm_div, sourceJacquetActualGauss_norm K hζ S₀ P hS 4 (by decide),
      Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    by_cases hx : x = 0
    · simp only [ite_eq_left hx]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (residue_norm_ge_one K S₀ P)), one_div]
      ring
    · simp only [ite_eq_right hx, norm_neg, norm_one, mul_one]
  · simp only [ite_eq_right hj4]
    by_cases hj0 : j = 0
    · simp only [ite_eq_left hj0]
      by_cases hx : x = 0
      · simp only [hx, MulChar.map_zero, mul_zero, norm_zero, eq_self, ite_true]
      · simp only [ite_eq_right hx, norm_mul, norm_neg, norm_div,
          sourceJacquetActualGauss_norm K hζ S₀ P hS 2 (by decide),
          Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
          character_norm_at_unit K S₀ P _ x hx, mul_one, one_div]
    · simp only [ite_eq_right hj0]
      by_cases hx : x = 0
      · simp only [hx, MulChar.map_zero, mul_zero, norm_zero, eq_self, ite_true]
      · have hj0' : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
        have hj4' : j.val ≠ 4 := fun h => hj4 (Fin.ext h)
        have hjlt := j.isLt
        have h1 : ¬ 6 ∣ j.val := by omega
        have h2 : ¬ 6 ∣ j.val + 2 := by omega
        simp only [ite_eq_right hx, norm_mul, sourceJacquetActualGauss_norm K hζ S₀ P hS _ h1,
          sourceJacquetActualGauss_norm K hζ S₀ P hS _ h2,
          character_norm_at_unit K S₀ P _ x hx, mul_one]

theorem sourceReflectionTameRotatedActive_norm_eq (j : Fin 6) (e : ℕ) (v : Lˣ)
    (hv : ν₀ (v : L) = 1) :
    ‖sourceReflectionTameRotatedActive K hζ S₀ P hS j e v‖ =
      if e = 0 then if j = 0 ∨ j = 4 then (Real.sqrt q)⁻¹ else 1
      else if j = 4 then (1 - q⁻¹) * sourceReflectionFrozenLocalWeight q e else 0 := by
  have hq := sourceJacquetPrimeNorm_pos K S₀ P
  have hv' := sourceKPLocalUnitResidue_ne_zero K P.val v hv
  rw [sourceReflectionTameRotatedActive_eq K hζ S₀ P hS j e v hv, norm_mul, norm_mul, norm_zpow,
    character_norm_at_unit K S₀ P χ₀ _ hv', one_zpow, one_mul,
    active_fourier_norm K hζ S₀ P hS, diagonal_norm K hζ S₀ P hS e v hv]
  by_cases he : e = 0
  · subst e
    simp only [Nat.zero_mod, Nat.zero_div, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one, eq_self, ite_true]
    by_cases hj : j = 4
    · simp [hj, hv', one_div]
    · simp [hj, hv']
  · simp only [ite_eq_right he]
    by_cases hj : j = 4
    · have hr : (q - 1) / Real.sqrt q = (1 - q⁻¹) * q ^ (1 / 2 : ℝ) := by
        rw [← Real.sqrt_eq_rpow]
        apply (div_eq_iff (Real.sqrt_pos.mpr hq).ne').mpr
        rw [mul_assoc, Real.mul_self_sqrt hq.le, sub_mul, one_mul, inv_mul_cancel₀ hq.ne']
      simp only [ite_eq_left hj, ite_true, hr, sourceReflectionFrozenLocalWeight, ite_eq_right he]
      by_cases h0 : e % 3 = 0
      · simp only [ite_eq_left h0, ite_eq_right (h0.trans_ne (by decide : (0 : ℕ) ≠ 1))]
        rw [mul_assoc, ← Real.rpow_add hq]
        congr 2
      · simp only [ite_eq_right h0]
        by_cases h1 : e % 3 = 1
        · simp only [ite_eq_left h1]
          rw [mul_assoc, ← Real.rpow_add hq]
          congr 2
          ring
        · simp only [ite_eq_right h1, mul_zero]
    · simp only [ite_eq_right hj, eq_self, ite_true, zero_mul]

theorem sourceReflectionTameRotatedActive_norm_le_frozen (j : Fin 6) (e : ℕ) (v : Lˣ)
    (hv : ν₀ (v : L) = 1) :
    ‖sourceReflectionTameRotatedActive K hζ S₀ P hS j e v‖ ≤ sourceReflectionFrozenLocalWeight q e := by
  have hq := sourceJacquetPrimeNorm_pos K S₀ P
  have hw : 0 ≤ sourceReflectionFrozenLocalWeight q e := by
    simpa only [sourceReflectionFrozenLocalTerm, zero_mul, neg_zero, Real.rpow_zero, mul_one]
      using sourceReflectionFrozenLocalTerm_nonneg hq.le 0 e
  rw [sourceReflectionTameRotatedActive_norm_eq K hζ S₀ P hS j e v hv]
  by_cases he : e = 0
  · rw [ite_eq_left he, sourceReflectionFrozenLocalWeight, ite_eq_left he]
    split_ifs
    · rw [← one_div]
      exact (div_le_one (Real.sqrt_pos.mpr hq)).mpr (Real.one_le_sqrt.mpr (residue_norm_ge_one K S₀ P))
    · exact le_rfl
  · rw [ite_eq_right he]
    split_ifs
    · exact mul_le_of_le_one_left hw (sub_le_self _ (inv_nonneg.mpr hq.le))
    · exact hw

end
end ArtinMatthews
