module

public import ArtinMatthews.ProbePrimeLocalHigher
public import ArtinMatthews.ProbePrimeLocalAbsent
public import ArtinMatthews.ProbePrimeSixthTable
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A single notation for all literal local coefficient cases. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped NumberField Classical
noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def probePrimeLocalCoefficient (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (t k J : ℕ) : ℂ :=
  match t, k with
  | 0, 0 => probePrimeLocalBothAbsent
  | 0, k + 1 => probePrimeLocalInnerAbsent K p χ k J
  | n + 1, 0 => probePrimeLocalCZero K p hp χ n J
  | n + 1, 1 => probePrimeLocalCOne K p hp χ n J
  | n + 1, k + 2 => probePrimeLocalHigher K p hp χ n (k + 1) J

theorem probePrimeLocalCoefficient_zero_zero (p : 𝓞 K) (hp : p ≠ 0)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (J : ℕ) :
    probePrimeLocalCoefficient K p hp χ 0 0 J = 1 :=
  probePrimeLocalBothAbsent_eq_one

theorem probePrimeLocalCoefficient_zero_succ (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (k r : ℕ) :
    probePrimeLocalCoefficient K p hp.ne_zero χ 0 (k + 1) (6 * r) =
      if r = 0 then 1 else 0 := by
  rw [probePrimeLocalCoefficient, probePrimeLocalInnerAbsent_eq K p hp]
  simp

theorem probePrimeLocalCoefficient_higher (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (n k J : ℕ) :
    probePrimeLocalCoefficient K p hp.ne_zero χ (n + 1) (k + 2) J = 0 := by
  rw [probePrimeLocalCoefficient]
  exact probePrimeLocalHigher_eq_zero K p hp χ n (k + 1) J (Nat.succ_pos k)

theorem probePrimeLocalCoefficient_zero_odd (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d k r : ℕ) :
    probePrimeLocalCoefficient K p hp.ne_zero χ (6 * d + 3) k (6 * r) = 0 := by
  have ht : 6 * d + 3 = (6 * d + 2) + 1 := by omega
  rw [ht]
  cases k with
  | zero =>
      exact probePrimeLocalCZero_off_classes K p hp χ hχ (6 * d + 2) r (by omega) (by omega)
  | succ k =>
      cases k with
      | zero =>
          exact probePrimeLocalCOne_off_classes K p hp χ hχ hminus (6 * d + 2) r (by omega) (by omega)
      | succ k => exact probePrimeLocalCoefficient_higher K p hp χ _ k _

theorem probePrimeLocalCoefficient_one_odd (p : 𝓞 K) (hp : Prime p)
    (χ : MulChar ((𝓞 K) ⧸ Ideal.span {p}) ℂ) (hχ : orderOf χ = 6)
    (hminus : χ (-1) = 1) (d k r : ℕ) :
    probePrimeLocalCoefficient K p hp.ne_zero χ (6 * d + 4) k (6 * r) = 0 := by
  have ht : 6 * d + 4 = (6 * d + 3) + 1 := by omega
  rw [ht]
  cases k with
  | zero =>
      exact probePrimeLocalCZero_off_classes K p hp χ hχ (6 * d + 3) r (by omega) (by omega)
  | succ k =>
      cases k with
      | zero =>
          exact probePrimeLocalCOne_off_classes K p hp χ hχ hminus (6 * d + 3) r (by omega) (by omega)
      | succ k => exact probePrimeLocalCoefficient_higher K p hp χ _ k _

end

end ArtinMatthews.VaryingKummerAnalytic
