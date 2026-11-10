module

public import OAI.NumberTheory.DirichletL.Hecke.FiniteDeletion
public import OAI.NumberTheory.DirichletL.Hecke.LogarithmicInput
public import ArtinMatthews.CubicReciprocityNonprincipalCharacterBase
public import ArtinMatthews.CubicReciprocityNonprincipalCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import OAI.NumberTheory.DirichletL.Hecke.Euler
public import OAI.NumberTheory.DirichletL.Hecke.IdealOperations


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial vertical growth after genuine primitive-conductor descent.
The original cubic character keeps its inflated modulus throughout. -/

noncomputable section
open scoped BigOperators

namespace ArtinMatthews

open OAI OAI.SevenEighths HeckeFamily

/-- A deleted finite Euler product has a height-independent bound on the
positive half-plane. No reciprocal or lower bound is asserted. -/
theorem deletedEulerProduct_norm_le_two_pow {ι : Type*} (S : Finset ι)
    (N : ι → ℝ) (a : ι → ℂ)
    (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖EulerFactors.deletedProduct S N a s‖ ≤ (2 : ℝ) ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [EulerFactors.deletedProduct]
  | @insert p S hp ih =>
    have hNS : ∀ q ∈ S, 1 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have haS : ∀ q ∈ S, ‖a q‖ ≤ 1 := fun q hq => ha q (Finset.mem_insert_of_mem hq)
    have hterm := EulerFactors.norm_term_lt_one (hN p (Finset.mem_insert_self p S))
      (ha p (Finset.mem_insert_self p S)) hs
    have hfactor : ‖EulerFactors.factor (N p) (a p) s‖ ≤ 2 := by
      have h := norm_sub_le (1 : ℂ) (a p * (N p : ℂ) ^ (-s))
      simp only [norm_one] at h
      exact h.trans (by linarith)
    have he : EulerFactors.deletedProduct (insert p S) N a s =
        EulerFactors.factor (N p) (a p) s * EulerFactors.deletedProduct S N a s := by
      simp only [EulerFactors.deletedProduct, Finset.prod_insert hp]
    rw [he, norm_mul, Finset.card_insert_of_notMem hp, pow_succ]
    calc
      _ ≤ 2 * (2 : ℝ) ^ S.card :=
        mul_le_mul hfactor (ih hNS haS) (norm_nonneg _) (by norm_num)
      _ = _ := by ring

/-- The actual deleted-prime product from conductor descent is bounded in
terms of the fixed original modulus alone. -/
theorem heckeDeletedFactors_norm_le (M : Ideal O) (ψ : Character)
    {s : ℂ} (hs : 0 < s.re) :
    ‖HeckeFiniteDeletion.factors M ψ s‖ ≤
      (2 : ℝ) ^ (SmoothMobiusCorrection.primeSet M).card := by
  apply deletedEulerProduct_norm_le_two_pow
  · intro P _
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < (2 : ℕ))
      (SmoothMobiusCorrection.prime_norm_two_le P))
  · intro P _
    exact idealCoeff_norm_le_one ψ P.val
  · exact hs

/-- Genuine primitive descent preserves nonprincipality and gives the exact
finite Euler-factor identity, including at `s=1` for a nonprincipal source. -/
theorem exists_nonprincipal_primitive_hecke_descent (χ : Character)
    (hχ : χ.residue ≠ 1) :
    ∃ ψ : Character, χ.modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue ≠ 1 ∧
      ψ.modulus.absNorm ≤ χ.modulus.absNorm ∧
      ∀ s : ℂ, 0 < s.re → LFunction χ s =
        LFunction ψ s * HeckeFiniteDeletion.factors χ.modulus ψ s := by
  obtain ⟨ψ, hmod, hp, hnorm, hmask⟩ := exists_primitive_character χ
  refine ⟨ψ, hmod, hp, ?_, hnorm, ?_⟩
  · exact fun h => hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  · intro s hs
    exact HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

/-- A positive, explicit constant depending on the fixed original character.
The deleted prime factors are those of its actual inflated modulus. -/
def heckeImprimitiveGrowthConstant (χ : Character) : ℝ :=
  1 + HeckeLogarithmicInput.uniformConstant * (χ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) *
    (2 : ℝ) ^ (SmoothMobiusCorrection.primeSet χ.modulus).card

theorem heckeImprimitiveGrowthConstant_pos (χ : Character) :
    0 < heckeImprimitiveGrowthConstant χ := by
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  unfold heckeImprimitiveGrowthConstant
  positivity

/-- Fixed-character polynomial growth on the positive half-plane, obtained
from the primitive associate and its finite deleted Euler product. -/
theorem nonprincipal_hecke_LFunction_right_growth (χ : Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ heckeImprimitiveGrowthConstant χ * (3 + |s.im|) ^ 2 := by
  obtain ⟨ψ, _, hp, hψ, hnorm, hidentity⟩ :=
    exists_nonprincipal_primitive_hecke_descent χ hχ
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  have hnormpow : (ψ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) ≤
      (χ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hnorm) (by norm_num)
  have hprimitive := HeckeLogarithmicInput.regular_right_growth ψ hp
    (show -(1 / 10 : ℝ) ≤ s.re by linarith)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hprimitive
  have hbound : ‖LFunction ψ s‖ ≤ HeckeLogarithmicInput.uniformConstant *
      (χ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) * (3 + |s.im|) ^ 2 :=
    hprimitive.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnormpow hU) (sq_nonneg _))
  rw [hidentity s hs, norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant *
        (χ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) * (3 + |s.im|) ^ 2) *
        (2 : ℝ) ^ (SmoothMobiusCorrection.primeSet χ.modulus).card :=
      mul_le_mul hbound (heckeDeletedFactors_norm_le χ.modulus ψ hs)
        (norm_nonneg _) (by positivity)
    _ = (HeckeLogarithmicInput.uniformConstant *
        (χ.modulus.absNorm : ℝ) ^ (3 / 5 : ℝ) *
        (2 : ℝ) ^ (SmoothMobiusCorrection.primeSet χ.modulus).card) *
        (3 + |s.im|) ^ 2 := by ring
    _ ≤ heckeImprimitiveGrowthConstant χ * (3 + |s.im|) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      unfold heckeImprimitiveGrowthConstant
      linarith

/-- The same bound for the regular function used by the logarithmic-input
API. Its nonprincipal branch is the actual Hecke `L`-function. -/
theorem nonprincipal_hecke_regular_right_growth (χ : Character)
    (hχ : χ.residue ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖HeckeLogarithmicInput.regular χ s‖ ≤
      heckeImprimitiveGrowthConstant χ * (3 + |s.im|) ^ 2 := by
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal χ hχ]
  exact nonprincipal_hecke_LFunction_right_growth χ hχ hs

/-- The actual cubic numerator character inherits polynomial growth without
any assertion that its convenient modulus `(9A)` is primitive. -/
theorem cubicNumeratorHeckeCharacter_right_growth (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein, y ^ 3 =
      (A : OAI.CubicFirstMoment.Eisenstein)) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction (cubicNumeratorHeckeCharacter A hA) s‖ ≤
      heckeImprimitiveGrowthConstant (cubicNumeratorHeckeCharacter A hA) *
        (3 + |s.im|) ^ 2 :=
  nonprincipal_hecke_LFunction_right_growth _
    (cubicNumeratorHeckeCharacter_nonprincipal A hA hnoncube) hs

end ArtinMatthews
