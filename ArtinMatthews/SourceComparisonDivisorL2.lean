module

public import ArtinMatthews.SourceComparisonMarkedDivisors
public import ArtinMatthews.GiantCandidateAllocationWeights
public import ArtinMatthews.SourceComparisonDivisorMass
public import ArtinMatthews.SourceComparisonHitMoments
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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

/-! A quantitative squared error for the actual truncated marked model.
The estimate is uniform over every bounded complex test of the ordered lists. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

variable {G : Type*} [Fintype G]

private theorem weightedTail_choose_bound (P S : Finset ℕ) (θ : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (k n : ℕ) :
    markedWeightedTail P S θ k n ≤
      if S ⊆ activeDivisors P n then ((bandCount P n).choose k : ℝ) else 0 := by
  classical
  by_cases hs : S ⊆ activeDivisors P n
  · rw [ite_eq_left hs, markedWeightedTail, markedIndexedDivisorPolynomial, ← sum_filter]
    let T := ((P \ S).powersetCard k).filter (fun T => (∏ p ∈ S ∪ T, p) ∣ n)
    have hsub : T ⊆ (activeDivisors P n).powersetCard k := by
      intro A hA
      obtain ⟨hA, hd⟩ := mem_filter.mp hA
      obtain ⟨hA, hc⟩ := mem_powersetCard.mp hA
      refine mem_powersetCard.mpr ⟨?_, hc⟩
      intro p hp
      exact mem_filter.mpr ⟨(mem_sdiff.mp (hA hp)).1,
        (dvd_prod_of_mem id (mem_union_right _ hp)).trans hd⟩
    calc
      _ ≤ ∑ _A ∈ T, (1 : ℝ) := by
        apply sum_le_sum
        intro A hA
        have hA' := (mem_powersetCard.mp (mem_filter.mp hA).1).1
        exact prod_le_one₀ (fun p hp => (hθ p (mem_sdiff.mp (hA' hp)).1).1)
          (fun p hp => (hθ p (mem_sdiff.mp (hA' hp)).1).2)
      _ = (T.card : ℝ) := by simp
      _ ≤ (((activeDivisors P n).powersetCard k).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = _ := by rw [card_powersetCard, bandCount]
  · rw [markedWeightedTail_eq P S hP hS, ite_eq_right hs, ite_eq_right hs]

def sourceComparisonMarkFactorialMass (P : G → Finset ℕ) (t : G → ℕ) : ℝ :=
  (∏ g, ((t g).factorial : ℝ)) / sourceComparisonMarkMass P t

private theorem comparisonChoice_selected_hits (P : G → Finset ℕ) (t : G → ℕ)
    {l : (g : G) → Fin (t g) → ℕ} (hl : l ∈ sourceComparisonMarkChoices P t) (n : ℕ) :
    representedArraySelected l ⊆ activeDivisors (univ.biUnion P) n ↔ ∀ g i, l g i ∣ n := by
  have hm := ((mem_sourceComparisonMarkChoices P t l).mp hl).1
  unfold representedArraySelected
  rw [selected_union_active_iff univ P _ (fun g _ => representedChoiceSet_subset (hm g))]
  simp only [mem_univ, true_implies, representedChoiceSet_active_iff (hm _)]

private theorem comparisonHitChoices_card_le (P : G → Finset ℕ) (t : G → ℕ)
    (n : ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j)) :
    ((sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t).card : ℝ) ≤
      (∏ g, ((t g).factorial : ℝ)) * Real.exp (bandCount (univ.biUnion P) n) := by
  classical
  have hcard : (sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t).card ≤
      ∏ g, (bandCount (P g) n) ^ t g := by
    unfold sourceComparisonMarkChoices
    apply (card_filter_le _ _).trans_eq
    simp only [representedArrayChoices, Fintype.card_piFinset, prod_const, card_univ,
      Fintype.card_fin, bandCount]
  calc
    _ ≤ ∏ g, ((bandCount (P g) n : ℝ)) ^ t g := by exact_mod_cast hcard
    _ ≤ _ := by
      rw [giantCandidateBandCount_union P hdis, Nat.cast_sum, Real.exp_sum, ← prod_mul_distrib]
      apply prod_le_prod₀ (fun _ _ => pow_nonneg (Nat.cast_nonneg _) _)
      intro g _
      have hfac : 0 < ((t g).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      exact ((div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (bandCount (P g) n : ℝ) (Nat.cast_nonneg _) (t g))).trans_eq
        (mul_comm _ _)

theorem sourceComparisonDivisorModel_choose_error (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) (k n : ℕ) :
    ‖sourceComparisonMarkWeight P t q b n - sourceComparisonDivisorModel P t q b k n‖ ≤
      sourceComparisonMarkFactorialMass P t * Real.exp (bandCount (univ.biUnion P) n) *
        ((bandCount (univ.biUnion P) n).choose (k + 1) : ℝ) := by
  classical
  let V := sourceComparisonMarkMass P t
  let C : ℝ := ((bandCount (univ.biUnion P) n).choose (k + 1) : ℝ)
  let D := sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t
  have hV₀ : 0 < V := sourceComparisonMarkMass_pos P t hV
  have hC : 0 ≤ C := Nat.cast_nonneg _
  refine (sourceComparisonDivisorModel_pointwise_error P t q hdis hq hP b k n).trans ?_
  calc
    _ ≤ ∑ l ∈ sourceComparisonMarkChoices P t, ‖sourceComparisonMarkCoefficient P t b l‖ *
        (if ∀ g i, l g i ∣ n then C else 0) := by
      apply sum_le_sum
      intro l hl
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have ht := weightedTail_choose_bound _ _ _ hP
        (sourceComparisonMarkChoices_selected_subset P t hl)
        (fun _ hp => sourceComparisonMarkResidualDamping_bounds P q hdis hq hp) (k + 1) n
      rwa [if_congr (comparisonChoice_selected_hits P t hl n) rfl rfl] at ht
    _ = ∑ l ∈ D, ‖sourceComparisonMarkCoefficient P t b l‖ * C := by
      simp_rw [mul_ite, mul_zero]
      rw [← sum_filter, ← sourceComparisonMarkChoices_active_filter]
    _ ≤ ∑ _l ∈ D, (1 / V) * C := by
      apply sum_le_sum
      intro l hl
      have hl' : l ∈ sourceComparisonMarkChoices P t := by
        change l ∈ sourceComparisonMarkChoices (fun g => activeDivisors (P g) n) t at hl
        rw [sourceComparisonMarkChoices_active_filter] at hl
        exact (mem_filter.mp hl).1
      apply mul_le_mul_of_nonneg_right _ hC
      rw [sourceComparisonMarkCoefficient, norm_div, Complex.norm_real, Real.norm_of_nonneg hV₀.le]
      exact div_le_div_of_nonneg_right (hb l hl') hV₀.le
    _ = ((D.card : ℝ) / V) * C := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact (div_le_div_of_nonneg_right (comparisonHitChoices_card_le P t n hdis) hV₀.le).trans_eq
        (by unfold sourceComparisonMarkFactorialMass V; ring)

private theorem choose_square_bound (r h : ℕ) :
    ((r.choose h : ℕ) : ℝ) ^ 2 ≤ (8 : ℝ) ^ r / (2 : ℝ) ^ h := by
  by_cases hh : h ≤ r
  · have hc : (r.choose h : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast Nat.choose_le_two_pow r h
    calc
      _ ≤ ((2 : ℝ) ^ r) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
      _ = (4 : ℝ) ^ r := by rw [← pow_mul, Nat.mul_comm r 2, pow_mul]; norm_num
      _ ≤ _ := by
        apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
        rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hh) (by positivity)
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hh), Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity

theorem sourceComparisonDivisorModel_l2_error (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j)) (hq : ∀ g, 0 ≤ q g ∧ q g ≤ 1)
    (hV : ∀ g, 0 < bandReciprocalMass (P g)) (hP : ∀ p ∈ univ.biUnion P, p.Prime)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ)
    (hb : ∀ l ∈ sourceComparisonMarkChoices P t, ‖b l‖ ≤ 1) (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ‖sourceComparisonMarkWeight P t q b n -
      sourceComparisonDivisorModel P t q b k n‖ ^ 2) ≤
      (N : ℝ) * (sourceComparisonMarkFactorialMass P t) ^ 2 /
        (2 : ℝ) ^ (k + 1) *
        Real.exp ((8 * Real.exp 2 - 1) * ∑ p ∈ univ.biUnion P, 1 / (p : ℝ)) := by
  let A := sourceComparisonMarkFactorialMass P t
  let B : ℝ := 8 * Real.exp 2
  have hB : 1 ≤ B := by
    have he : 1 ≤ Real.exp 2 := Real.one_le_exp_iff.mpr (by norm_num)
    dsimp only [B]
    linarith
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (A ^ 2 / (2 : ℝ) ^ (k + 1)) *
        B ^ bandCount (univ.biUnion P) n := by
      apply sum_le_sum
      intro n _
      let r := bandCount (univ.biUnion P) n
      have he : (Real.exp (r : ℝ)) ^ 2 = (Real.exp 2) ^ r := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      calc
        _ ≤ (A * Real.exp r * (r.choose (k + 1) : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (sourceComparisonDivisorModel_choose_error P t q hdis hq hV hP b hb k n) 2
        _ = A ^ 2 * (Real.exp r) ^ 2 * (r.choose (k + 1) : ℝ) ^ 2 := by ring
        _ ≤ A ^ 2 * (Real.exp r) ^ 2 * ((8 : ℝ) ^ r / (2 : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left (choose_square_bound r (k + 1)) (by positivity)
        _ = _ := by
          change _ = (A ^ 2 / (2 : ℝ) ^ (k + 1)) * B ^ r
          dsimp only [B]
          rw [he, mul_pow]
          ring
    _ = (A ^ 2 / (2 : ℝ) ^ (k + 1)) * ∑ n ∈ Ioc 0 N, B ^ bandCount (univ.biUnion P) n :=
      (mul_sum ..).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sourceComparisonHitMoment_le _ hP hB N) (by positivity)).trans_eq
      (by dsimp only [A, B]; ring)

end
end ArtinMatthews
