module

public import ArtinMatthews.GiantMarkedResidual
public import Mathlib.Analysis.CStarAlgebra.Classes
public import ArtinMatthews.SourceComparisonSmoothProgression
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


set_option backward.privateInPublic true
@[expose] public section

/-! The complete residue main term cancels against the literal reciprocal
giant-prime center. The retained complex divisor coefficients keep their signs. -/
namespace ArtinMatthews
open Finset MeasureTheory
open scoped BigOperators
noncomputable section

def sourceComparisonLongReciprocal (L : Finset ℕ) : ℝ :=
  ∑ p ∈ L, 1 / (p : ℝ)

def sourceComparisonLongCenter (L : Finset ℕ) (n : ℕ) : ℂ :=
  (giantWindowDivisorCount L n - sourceComparisonLongReciprocal L : ℝ)

def sourceComparisonDivisorSum (I : Finset ℕ) (F : ℕ → ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ I, if d ∣ n then F n else 0

private theorem comparisonCenter_single_divisor (I L : Finset ℕ) (F : ℕ → ℂ)
    (d : ℕ) (c : ℂ) (hcop : ∀ p ∈ L, p.Coprime d) :
    (∑ n ∈ I, F n * sourceComparisonLongCenter L n * (if d ∣ n then c else 0)) =
      c * ((∑ p ∈ L, sourceComparisonDivisorSum I F (p * d)) -
        (sourceComparisonLongReciprocal L : ℂ) * sourceComparisonDivisorSum I F d) := by
  classical
  simp only [sourceComparisonDivisorSum]
  rw [sum_comm (s := L) (t := I), mul_sum, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro n _
  by_cases hd : d ∣ n
  · have he : (∑ p ∈ L, if p * d ∣ n then F n else 0) =
        F n * (giantWindowDivisorCount L n : ℂ) := by
      rw [giantWindowDivisorCount, Complex.ofReal_sum, mul_sum]
      apply sum_congr rfl
      intro p hp
      have hh : p * d ∣ n ↔ p ∣ n := ⟨fun h => (dvd_mul_right p d).trans h,
        fun h => (hcop p hp).mul_dvd_of_dvd_of_dvd h hd⟩
      by_cases hp' : p ∣ n
      · simp [hp', hh.mpr hp']
      · have hneg : ¬ p * d ∣ n := fun h => hp' (hh.mp h)
        simp [hp', hneg]
    rw [ite_eq_left hd, ite_eq_left hd, he, sourceComparisonLongCenter, Complex.ofReal_sub]
    ring
  · have he : (∑ p ∈ L, if p * d ∣ n then F n else 0) = 0 := by
      apply sum_eq_zero
      intro p _
      exact ite_eq_right (fun h => hd ((dvd_mul_of_dvd_right (dvd_refl d) p).trans h))
    simp only [ite_eq_right hd, he, mul_zero, sub_zero]

theorem sourceComparisonCenteredDivisorSum_expand {ι : Type*}
    (I L : Finset ℕ) (D : Finset ι) (d : ι → ℕ) (c : ι → ℂ) (F : ℕ → ℂ)
    (hcop : ∀ j ∈ D, ∀ p ∈ L, p.Coprime (d j)) :
    (∑ n ∈ I, F n * sourceComparisonLongCenter L n *
      (∑ j ∈ D, if d j ∣ n then c j else 0)) =
      ∑ j ∈ D, c j * ((∑ p ∈ L, sourceComparisonDivisorSum I F (p * d j)) -
        (sourceComparisonLongReciprocal L : ℂ) * sourceComparisonDivisorSum I F (d j)) := by
  classical
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  exact comparisonCenter_single_divisor I L F (d j) (c j) (hcop j hj)

private theorem comparisonCenteredBracket_bound (I L : Finset ℕ) (F : ℕ → ℂ)
    (d : ℕ) (J : ℂ) (E : ℝ)
    (h0 : ‖sourceComparisonDivisorSum I F d - J / (d : ℂ)‖ ≤ E)
    (hL : ∀ p ∈ L, ‖sourceComparisonDivisorSum I F (p * d) - J / (p * d : ℕ)‖ ≤ E) :
    ‖(∑ p ∈ L, sourceComparisonDivisorSum I F (p * d)) -
      (sourceComparisonLongReciprocal L : ℂ) * sourceComparisonDivisorSum I F d‖ ≤
        ((L.card : ℝ) + sourceComparisonLongReciprocal L) * E := by
  let C := sourceComparisonLongReciprocal L
  have hC : 0 ≤ C := sum_nonneg (fun _ _ => by positivity)
  have hmain : (∑ p ∈ L, J / (p * d : ℕ)) = (C : ℂ) * (J / (d : ℂ)) := by
    unfold C sourceComparisonLongReciprocal
    rw [Complex.ofReal_sum, sum_mul]
    apply sum_congr rfl
    intro p _
    simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
    push_cast
    ring
  have he :
      (∑ p ∈ L, sourceComparisonDivisorSum I F (p * d)) -
        (C : ℂ) * sourceComparisonDivisorSum I F d =
      (∑ p ∈ L, (sourceComparisonDivisorSum I F (p * d) - J / (p * d : ℕ))) -
        (C : ℂ) * (sourceComparisonDivisorSum I F d - J / (d : ℂ)) := by
    rw [sum_sub_distrib, hmain, mul_sub]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hsum : ‖∑ p ∈ L, (sourceComparisonDivisorSum I F (p * d) - J / (p * d : ℕ))‖ ≤
      (L.card : ℝ) * E := by
    apply (norm_sum_le _ _).trans
    exact (sum_le_sum hL).trans_eq (by rw [sum_const, nsmul_eq_mul])
  have hzero : ‖(C : ℂ) * (sourceComparisonDivisorSum I F d - J / (d : ℂ))‖ ≤ C * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_left h0 hC
  exact (add_le_add hsum hzero).trans_eq (by ring)

theorem sourceComparisonCenteredDivisorSum_bound {ι : Type*}
    (L : Finset ℕ) (D : Finset ι) (d : ι → ℕ) (c : ι → ℂ)
    (k : ℕ) [NeZero k] (A : ZMod k → ℂ) (hA : ∀ a, ‖A a‖ ≤ 1)
    (hD : ∀ j ∈ D, 0 < d j ∧ (d j).Coprime k)
    (hL : ∀ p ∈ L, 0 < p ∧ p.Coprime k)
    (hcop : ∀ j ∈ D, ∀ p ∈ L, p.Coprime (d j))
    (f : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) :
    ‖∑ n ∈ Icc 0 ⌊T⌋₊, (A (n : ZMod k) * f n) * sourceComparisonLongCenter L n *
      (∑ j ∈ D, if d j ∣ n then c j else 0)‖ ≤
      (((L.card : ℝ) + sourceComparisonLongReciprocal L) *
        ((3 * (k : ℝ)) * ∫ t in Set.Ioc 0 T, ‖deriv f t‖)) * ∑ j ∈ D, ‖c j‖ := by
  classical
  let F (n : ℕ) := A (n : ZMod k) * f n
  let I := Icc 0 ⌊T⌋₊
  let J := sourceComparisonResidueMean k A * ∫ t in Set.Ioc 0 T, f t
  let E := (3 * (k : ℝ)) * ∫ t in Set.Ioc 0 T, ‖deriv f t‖
  have hprog (v : ℕ) (hv : 0 < v) (hvk : v.Coprime k) :
      ‖sourceComparisonDivisorSum I F v - J / (v : ℂ)‖ ≤ E := by
    have h := sourceComparisonDivisorSmoothPhase_error v k hv hvk A hA f hT hf hderiv hfT
    have he : (sourceComparisonResidueMean k A / (v : ℂ)) * ∫ t in Set.Ioc 0 T, f t =
        J / (v : ℂ) := by dsimp only [J]; ring
    rw [he] at h
    exact h
  change ‖∑ n ∈ I, F n * sourceComparisonLongCenter L n *
    (∑ j ∈ D, if d j ∣ n then c j else 0)‖ ≤ _
  rw [sourceComparisonCenteredDivisorSum_expand I L D d c F hcop]
  apply (norm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  rw [norm_mul, mul_comm (((L.card : ℝ) + sourceComparisonLongReciprocal L) * E)]
  exact mul_le_mul_of_nonneg_left
    (comparisonCenteredBracket_bound I L F (d j) J E (hprog _ (hD j hj).1 (hD j hj).2)
      (fun p hp => hprog _ (Nat.mul_pos (hL p hp).1 (hD j hj).1)
        ((hL p hp).2.mul_left (hD j hj).2))) (norm_nonneg _)

end
end ArtinMatthews
