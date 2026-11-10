module

public import ArtinMatthews.IdealGroupedAtom
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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


set_option backward.privateInPublic true
@[expose] public section

/-! The per-group factorial atom loss is a fixed power of L when the
number of groups is at most C₀ log L. Its exponent is independent of J. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Fintype G] [DecidableEq G]

def idealGroupedBudgetExponent (m : ℕ) (C₀ v₀ : ℝ) : ℝ :=
  C₀ * (Real.log (m.factorial : ℝ) + m * Real.log (max 1 v₀⁻¹))

omit [DecidableEq G] in
theorem idealGroupedAtomBudget_le (P : G → Finset ℕ) (k : G → ℕ)
    {m : ℕ} {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hV : ∀ g, v₀ ≤ bandReciprocalMass (P g)) (hk : ∀ g, k g ≤ m) :
    idealGroupedAtomBudget P k ≤
      ((m.factorial : ℝ) * (max 1 v₀⁻¹)^m)^(Fintype.card G) := by
  have hb : (∏ g, ((k g).factorial : ℝ) * (bandReciprocalMass (P g))⁻¹ ^ (k g)) ≤
      ∏ _g : G, ((m.factorial : ℝ) * (max 1 v₀⁻¹)^m) := by
    apply prod_le_prod₀
    · intro g _
      exact mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (inv_nonneg.mpr (hv₀.trans_le (hV g)).le) _)
    · intro g _
      have hVpos : 0 < bandReciprocalMass (P g) := hv₀.trans_le (hV g)
      have hbase : (bandReciprocalMass (P g))⁻¹ ≤ max 1 v₀⁻¹ :=
        (inv_anti₀ hv₀ (hV g)).trans (le_max_right _ _)
      have hp : (bandReciprocalMass (P g))⁻¹ ^ (k g) ≤ (max 1 v₀⁻¹)^m := by
        exact (pow_le_pow_left₀ (inv_nonneg.mpr hVpos.le) hbase _).trans
          (pow_le_pow_right₀ (le_max_left _ _) (hk g))
      exact mul_le_mul (by exact_mod_cast Nat.factorial_le (hk g)) hp
        (pow_nonneg (inv_nonneg.mpr hVpos.le) _) (by positivity)
  simpa only [idealGroupedAtomBudget, prod_const, card_univ] using hb


omit [DecidableEq G] in
theorem idealGroupedAtomBudget_power (P : G → Finset ℕ) (k : G → ℕ)
    {m : ℕ} {C₀ v₀ L : ℝ} (hv₀ : 0 < v₀) (hL : 1 ≤ L)
    (hV : ∀ g, v₀ ≤ bandReciprocalMass (P g)) (hk : ∀ g, k g ≤ m)
    (hcard : (Fintype.card G : ℝ) ≤ C₀*Real.log L) :
    idealGroupedAtomBudget P k ≤ L^(idealGroupedBudgetExponent m C₀ v₀) := by
  let B : ℝ := (m.factorial : ℝ) * (max 1 v₀⁻¹)^m
  have hf : 1 ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hp : 1 ≤ (max 1 v₀⁻¹)^m := one_le_pow₀ (le_max_left _ _)
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hBexp : B^(Fintype.card G) = Real.exp ((Fintype.card G : ℝ)*Real.log B) := by
    rw [Real.exp_nat_mul, Real.exp_log hBpos]
  have hlog : Real.log B = Real.log (m.factorial : ℝ) + m*Real.log (max 1 v₀⁻¹) := by
    dsimp only [B]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
  calc
    _ ≤ B^(Fintype.card G) := idealGroupedAtomBudget_le P k hv₀ hV hk
    _ = Real.exp ((Fintype.card G : ℝ)*Real.log B) := hBexp
    _ ≤ Real.exp ((C₀*Real.log L)*Real.log B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hlogB)
    _ = _ := by
      rw [Real.rpow_def_of_pos hLpos, idealGroupedBudgetExponent, hlog]
      congr 1
      ring

end
end ArtinMatthews
