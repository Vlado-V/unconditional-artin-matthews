module

public import ArtinMatthews.RoughCharacterDensity
public import Mathlib.Data.FunLike.Fintype
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import ArtinMatthews.RoughBonferroniInterval
public import ArtinMatthews.RoughBonferroniLayerBounds
public import ArtinMatthews.RoughCharacterMultiples
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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

/-! Actual finite rough-character counts with explicit Bonferroni layer and
endpoint errors, obtained from genuine complete-period cancellation. -/
noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators Classical

private theorem rough_norm_sub_triangle (a b c : ℂ) :
    ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
  simpa only [dist_eq_norm] using dist_triangle a b c

def roughCharacterIocSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (M N : ℕ) : ℂ :=
  ∑ n ∈ Ioc M N, (if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0) * χ (n : ZMod q)

def roughOrdinaryIocSum (P : Finset ℕ) (M N : ℕ) : ℂ :=
  ∑ n ∈ Ioc M N, if ∀ p ∈ P, ¬ p ∣ n then (1 : ℂ) else 0

def roughCharacterTruncationIocSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (r M N : ℕ) : ℂ :=
  ∑ n ∈ Ioc M N, roughDivisorPolynomial P r n * χ (n : ZMod q)

def roughOrdinaryTruncationIocSum (P : Finset ℕ) (r M N : ℕ) : ℂ :=
  ∑ n ∈ Ioc M N, roughDivisorPolynomial P r n

theorem roughCharacterTruncationIocSum_reindex {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Finset ℕ) (r M N : ℕ) :
    roughCharacterTruncationIocSum χ P r M N =
      ∑ D ∈ roughTruncationSubsets P r, (-1 : ℂ) ^ D.card *
        ∑ n ∈ Ioc M N, if roughSubsetDivisor D ∣ n then χ (n : ZMod q) else 0 := by
  unfold roughCharacterTruncationIocSum roughDivisorPolynomial
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem roughCharacterTruncationIocSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (P : Finset ℕ) (r M N : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    ‖roughCharacterTruncationIocSum χ P r M N‖ ≤
      (q : ℝ) * (roughTruncationSubsets P r).card := by
  rw [roughCharacterTruncationIocSum_reindex]
  calc
    _ ≤ ∑ D ∈ roughTruncationSubsets P r,
        ‖(-1 : ℂ) ^ D.card *
          ∑ n ∈ Ioc M N, if roughSubsetDivisor D ∣ n then χ (n : ZMod q) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ roughTruncationSubsets P r, (q : ℝ) := by
      apply sum_le_sum
      intro D hD
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact rough_nonprincipal_character_multiples_norm_le χ hχ M N _
        (roughSubsetDivisor_pos D (fun p hp =>
          hprime p ((mem_powerset.mp (mem_filter.mp hD).1) hp)))
    _ = _ := by simp [mul_comm]

/-- The nonprincipal rough sum has no density term. -/
theorem rough_nonprincipal_character_Ioc_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (P : Finset ℕ) (r M N : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    ‖roughCharacterIocSum χ P M N‖ ≤
      ((N - M : ℕ) : ℝ) *
        (∑ D ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor D : ℝ)) +
      ((P.powersetCard (r + 1)).card : ℝ) +
      (q : ℝ) * (roughTruncationSubsets P r).card := by
  have he := roughDivisorPolynomial_weighted_Ioc_error_le P r M N hprime
    (fun n => χ (n : ZMod q)) (fun n _ => χ.norm_le_one _)
  have ht := roughCharacterTruncationIocSum_norm_le χ hχ P r M N hprime
  change ‖roughCharacterIocSum χ P M N - roughCharacterTruncationIocSum χ P r M N‖ ≤ _ at he
  have hh := rough_norm_sub_triangle (roughCharacterIocSum χ P M N)
    (roughCharacterTruncationIocSum χ P r M N) 0
  simp only [sub_zero] at hh
  exact hh.trans (add_le_add he ht)

theorem roughOrdinaryTruncationIocSum_reindex (P : Finset ℕ) (r M N : ℕ) :
    roughOrdinaryTruncationIocSum P r M N =
      ∑ D ∈ roughTruncationSubsets P r, (-1 : ℂ) ^ D.card *
        (((∑ n ∈ Ioc M N, if roughSubsetDivisor D ∣ n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  unfold roughOrdinaryTruncationIocSum roughDivisorPolynomial
  rw [sum_comm]
  apply sum_congr rfl
  intro D _
  rw [Complex.ofReal_sum, mul_sum]
  apply sum_congr rfl
  intro n _
  split_ifs <;> simp

theorem roughCharacterDensityTruncation_main_eq (P : Finset ℕ) (r M N : ℕ) :
    ((((N - M : ℕ) : ℝ) * roughCharacterDensityTruncation P r : ℝ) : ℂ) =
      ∑ D ∈ roughTruncationSubsets P r, (-1 : ℂ) ^ D.card *
        (((((N - M : ℕ) : ℝ) / (roughSubsetDivisor D : ℝ)) : ℝ) : ℂ) := by
  simp only [roughCharacterDensityTruncation, Complex.ofReal_mul, Complex.ofReal_sum, mul_sum,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
  apply sum_congr rfl
  intro D _
  ring

/-- Explicit endpoint error in the ordinary truncated divisor sum. -/
theorem roughOrdinaryTruncationIocSum_error_le (P : Finset ℕ) (r M N : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ‖roughOrdinaryTruncationIocSum P r M N -
      ((((N - M : ℕ) : ℝ) * roughCharacterDensityTruncation P r : ℝ) : ℂ)‖ ≤
      2 * (roughTruncationSubsets P r).card := by
  rw [roughOrdinaryTruncationIocSum_reindex, roughCharacterDensityTruncation_main_eq,
    ← sum_sub_distrib]
  calc
    _ ≤ ∑ D ∈ roughTruncationSubsets P r,
        ‖(-1 : ℂ) ^ D.card *
          (((∑ n ∈ Ioc M N, if roughSubsetDivisor D ∣ n then (1 : ℝ) else 0) : ℝ) : ℂ) -
          (-1 : ℂ) ^ D.card *
            (((((N - M : ℕ) : ℝ) / (roughSubsetDivisor D : ℝ)) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _D ∈ roughTruncationSubsets P r, (2 : ℝ) := by
      apply sum_le_sum
      intro D hD
      rw [← mul_sub, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact rough_interval_multiples_discrepancy_le M N _
        (roughSubsetDivisor_pos D (fun p hp =>
          hprime p ((mem_powerset.mp (mem_filter.mp hD).1) hp)))
    _ = _ := by simp [mul_comm]


/-- The actual ordinary rough count has its true Euler-density main term. -/
theorem rough_ordinary_Ioc_error_le (P : Finset ℕ) (r M N : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) :
    ‖roughOrdinaryIocSum P M N -
      ((((N - M : ℕ) : ℝ) * roughCharacterEulerDensity P : ℝ) : ℂ)‖ ≤
      2 * ((N - M : ℕ) : ℝ) *
        (∑ D ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor D : ℝ)) +
      ((P.powersetCard (r + 1)).card : ℝ) +
      2 * (roughTruncationSubsets P r).card := by
  let l : ℝ := (N - M : ℕ)
  let E : ℝ := ∑ D ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor D : ℝ)
  have he : ‖roughOrdinaryIocSum P M N - roughOrdinaryTruncationIocSum P r M N‖ ≤
      l * E + ((P.powersetCard (r + 1)).card : ℝ) := by
    simpa only [roughOrdinaryIocSum, roughOrdinaryTruncationIocSum, mul_one] using
      roughDivisorPolynomial_weighted_Ioc_error_le P r M N hprime
        (fun _ => (1 : ℂ)) (fun _ _ => by norm_num)
  have ht := roughOrdinaryTruncationIocSum_error_le P r M N hprime
  have hd : ‖((l * roughCharacterDensityTruncation P r : ℝ) : ℂ) -
      ((l * roughCharacterEulerDensity P : ℝ) : ℂ)‖ ≤ l * E := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ← mul_sub,
      abs_mul, abs_of_nonneg (show 0 ≤ l from Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_left (roughCharacterDensityTruncation_error_le P r hprime)
      (Nat.cast_nonneg _)
  calc
    _ ≤ ‖roughOrdinaryIocSum P M N - roughOrdinaryTruncationIocSum P r M N‖ +
        ‖roughOrdinaryTruncationIocSum P r M N -
          ((l * roughCharacterEulerDensity P : ℝ) : ℂ)‖ := rough_norm_sub_triangle _ _ _
    _ ≤ (l * E + ((P.powersetCard (r + 1)).card : ℝ)) +
        (2 * (roughTruncationSubsets P r).card + l * E) := by
      apply add_le_add he
      exact (rough_norm_sub_triangle (roughOrdinaryTruncationIocSum P r M N)
        ((l * roughCharacterDensityTruncation P r : ℝ) : ℂ)
        ((l * roughCharacterEulerDensity P : ℝ) : ℂ)).trans (add_le_add ht hd)
    _ = _ := by change (l * E + _) + (_ + l * E) = 2 * l * E + _ + _; ring

/-- Avoiding a set containing every prime divisor of the modulus forces
coprimality with that actual modulus. -/
theorem rough_avoid_coprime {q n : ℕ} (P : Finset ℕ)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ q → p ∈ P)
    (hn : ∀ p ∈ P, ¬ p ∣ n) : n.Coprime q := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro p hp hpq
  exact hn p (hcover p hp hpq)

/-- On the rough support, the actual principal character is identically one. -/
theorem rough_principal_character_Ioc_eq {q : ℕ} (P : Finset ℕ) (M N : ℕ)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ q → p ∈ P) :
    roughCharacterIocSum (1 : DirichletCharacter ℂ q) P M N = roughOrdinaryIocSum P M N := by
  unfold roughCharacterIocSum roughOrdinaryIocSum
  apply sum_congr rfl
  intro n _
  by_cases hn : ∀ p ∈ P, ¬ p ∣ n
  · rw [ite_eq_left hn, one_mul]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr (rough_avoid_coprime P hcover hn))
  · simp only [ite_eq_right hn, zero_mul]

/-- Genuine rough-character distribution with a single explicit error valid
for the principal and every nonprincipal character. -/
theorem rough_character_Ioc_error_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (r M N : ℕ)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ q → p ∈ P) :
    ‖roughCharacterIocSum χ P M N -
      (if χ = 1 then ((((N - M : ℕ) : ℝ) * roughCharacterEulerDensity P : ℝ) : ℂ) else 0)‖ ≤
      2 * ((N - M : ℕ) : ℝ) *
        (∑ D ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor D : ℝ)) +
      ((P.powersetCard (r + 1)).card : ℝ) +
      ((q : ℝ) + 2) * (roughTruncationSubsets P r).card := by
  by_cases hχ : χ = 1
  · subst χ
    rw [ite_eq_left rfl, rough_principal_character_Ioc_eq P M N hcover]
    apply (rough_ordinary_Ioc_error_le P r M N hprime).trans
    have hqk : (0 : ℝ) ≤ (q : ℝ) * (roughTruncationSubsets P r).card :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nlinarith
  · rw [ite_eq_right hχ, sub_zero]
    apply (rough_nonprincipal_character_Ioc_error_le χ hχ P r M N hprime).trans
    have he : 0 ≤ ((N - M : ℕ) : ℝ) *
        (∑ D ∈ P.powersetCard (r + 1), 1 / (roughSubsetDivisor D : ℝ)) := by positivity
    have hk : (0 : ℝ) ≤ (roughTruncationSubsets P r).card := Nat.cast_nonneg _
    nlinarith

/-- Explicit factorial and subset-size version of the actual distribution
bound, with no distribution estimate among its hypotheses. -/
theorem rough_character_Ioc_error_numeric {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (r M N v : ℕ)
    (hprime : ∀ p ∈ P, p.Prime) (hheight : ∀ p ∈ P, p ≤ v) (hv : 1 ≤ v)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ q → p ∈ P) :
    ‖roughCharacterIocSum χ P M N -
      (if χ = 1 then ((((N - M : ℕ) : ℝ) * roughCharacterEulerDensity P : ℝ) : ℂ) else 0)‖ ≤
      2 * ((N - M : ℕ) : ℝ) *
        ((∑ p ∈ P, 1 / (p : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) +
      (v : ℝ) ^ (r + 1) + ((q : ℝ) + 2) * (r + 1 : ℕ) * (v : ℝ) ^ r := by
  apply (rough_character_Ioc_error_le χ P r M N hprime hcover).trans
  have hcard : ((P.powersetCard (r + 1)).card : ℝ) ≤ (v : ℝ) ^ (r + 1) := by
    exact_mod_cast rough_layer_card_le_pow P (r + 1) v hprime hheight
  have htrunc : ((roughTruncationSubsets P r).card : ℝ) ≤ (r + 1 : ℕ) * (v : ℝ) ^ r := by
    exact_mod_cast roughTruncationSubsets_card_le_pow P r v hprime hheight hv
  calc
    _ ≤ 2 * ((N - M : ℕ) : ℝ) *
        ((∑ p ∈ P, 1 / (p : ℝ)) ^ (r + 1) / ((r + 1).factorial : ℝ)) +
        (v : ℝ) ^ (r + 1) + ((q : ℝ) + 2) * ((r + 1 : ℕ) * (v : ℝ) ^ r) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (rough_layer_reciprocal_mass_le_factorial P (r + 1))
          (by positivity)) hcard) (mul_le_mul_of_nonneg_left htrunc (by positivity))
    _ = _ := by ring

end ArtinMatthews
