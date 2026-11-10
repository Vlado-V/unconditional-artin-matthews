module

public import ArtinMatthews.MarkedArrayEulerModel
public import Mathlib.NumberTheory.Harmonic.Defs
public import ArtinMatthews.MarkedProgressionCoprime
public import ArtinMatthews.MarkedProgressionFamily
public import ArtinMatthews.MarkedProgressionResidualBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

/-! Actual marking-array progression errors. The array expansion, selected
union, repeated tuples, normalized coefficients, and Euler mean are all
concrete. Only elementary coefficient masses remain on the right. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

private theorem selected_card_le {ι : Type*} [Fintype ι] {a : ι → ℕ}
    (t : (i : ι) → Fin (a i) → ℕ) : (representedArraySelected t).card ≤ ∑ i, a i := by
  classical
  apply Finset.card_biUnion_le.trans
  apply Finset.sum_le_sum
  intro i _
  exact (Finset.card_image_le).trans_eq (by simp)

/-- Uniform finite parameters may replace the smaller individual selected
set and residual band in the exact quantitative progression estimate. -/
private theorem residual_uniform_bound (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R s : ℕ) (hs : S.card ≤ s)
    {y V N : ℝ} (hy : 0 < y) (hmin : ∀ p ∈ P, y ≤ (p : ℝ)) (hV : 0 ≤ V)
    (hmass : ∑ p ∈ P \ S, θ p / (p : ℝ) ≤ V)
    (hN : max 1 ((P \ S).card : ℝ) ≤ N)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
          Φ ((u : ℝ) / x) * markedWeightedResidual P S θ u) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1)) +
      (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        ((((s + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) /
        (∏ p ∈ S, p : ℕ) := by
  have h := marked_weighted_residual_rescaled_quantitative P S hP hS θ hθ m R
    hy hmin hV hmass Φ hx hT hΦ hderiv hΦT hΦ0
  have hI : 0 ≤ ∫ t in Set.Ioc 0 T, Φ t := integral_nonneg hΦ0
  have hVar : 0 ≤ ∫ t in Set.Ioc 0 T, |deriv Φ t| := integral_nonneg (fun _ => abs_nonneg _)
  have hH : 0 ≤ (harmonic R : ℝ) := by
    rw [← reciprocal_Icc_eq_harmonic]
    exact Finset.sum_nonneg (fun r _ => by positivity)
  have hN0 : 0 ≤ max 1 ((P \ S).card : ℝ) := le_trans (by norm_num) (le_max_left _ _)
  have hrnd : (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((P \ S).card : ℝ)) ^ (2 * m) +
        (max 1 ((P \ S).card : ℝ)) ^ (2 * m + 1)) ≤
      (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1)) := by
    gcongr
  have hloc : (((S.card + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
        2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial) ≤
      (((s + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
        2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial) := by
    gcongr
  apply h.trans
  calc
    _ ≤ (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * N ^ (2 * m) + N ^ (2 * m + 1)) +
      ((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (1 / (∏ p ∈ S, p : ℕ)) *
        ((((s + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hrnd (by positivity)
      · exact mul_le_mul_of_nonneg_left hloc (by positivity)
    _ = _ := by ring

/-- The actual marking-array progression discrepancy, including repeated
bands, is bounded by its explicit coefficient and reciprocal masses. -/
theorem marked_array_progression_error {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (ha : ∀ i, 0 < a i)
    (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hP : ∀ i p, p ∈ P i → p.Prime) (m R : ℕ)
    {y V : ℝ} (hy : 0 < y) (hmin : ∀ i p, p ∈ P i → y ≤ (p : ℝ))
    (hV : 0 ≤ V) (hmass : ∑ p ∈ Finset.univ.biUnion P, 1 / (p : ℝ) ≤ V)
    (Φ : ℝ → ℝ) {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) (hΦ : Differentiable ℝ Φ)
    (hderiv : Continuous (deriv Φ)) (hΦT : Φ T = 0) (hΦ0 : ∀ t, 0 ≤ Φ t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1),
          Φ ((u : ℝ) / x) * ∏ i, (bandWeight (P i) (W i) u) ^ a i) -
        ((x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ)) * representedArrayEulerMean P W a|) ≤
      ((R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv Φ t|) *
        (((2 * m + 1 : ℕ) : ℝ) * (max 1 ((Finset.univ.biUnion P).card : ℝ)) ^ (2 * m) +
          (max 1 ((Finset.univ.biUnion P).card : ℝ)) ^ (2 * m + 1))) *
        (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) +
      (((x * ∫ t in Set.Ioc 0 T, Φ t) * (harmonic R : ℝ)) *
        (((((∑ i, a i) + 2 * m : ℕ) : ℝ) / y) * Real.exp V +
          2 * (V ^ (2 * m + 1) / (2 * m + 1).factorial))) *
        (∑ t ∈ representedArrayChoices P a,
          |representedArrayCoefficient W a t| / (∏ p ∈ representedArraySelected t, p : ℕ)) := by
  classical
  let Q := Finset.univ.biUnion P
  let θ := representedArrayDamping Finset.univ P a (1 / 2)
  have hQ : ∀ p ∈ Q, p.Prime := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hP i p hi
  have hqmin : ∀ p ∈ Q, y ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact hmin i p hi
  have hθ : ∀ p ∈ Q, 0 ≤ θ p ∧ θ p ≤ 1 := fun p hp =>
    representedArrayDamping_mem_unitInterval Finset.univ P a (by norm_num) (by norm_num)
      (fun i _ j _ hij => hdis hij) hp
  have hsel (t) (ht : t ∈ representedArrayChoices P a) : representedArraySelected t ⊆ Q := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      representedChoiceSet_subset (Fintype.mem_piFinset.mp (Fintype.mem_piFinset.mp ht i)) hi⟩
  have hterm (t) (ht : t ∈ representedArrayChoices P a) :=
    residual_uniform_bound Q (representedArraySelected t) hQ (hsel t ht) θ hθ m R
      (∑ i, a i) (selected_card_le t) hy hqmin hV (by
        calc
          _ ≤ ∑ p ∈ Q \ representedArraySelected t, 1 / (p : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            exact div_le_div_of_nonneg_right (hθ p (Finset.mem_sdiff.mp hp).1).2 (Nat.cast_nonneg _)
          _ ≤ ∑ p ∈ Q, 1 / (p : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
            Finset.sdiff_subset (fun p _ _ => by positivity)
          _ ≤ V := hmass)
      (N := max 1 (Q.card : ℝ)) (by
        apply max_le_max_left
        exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := Q) (t := representedArraySelected t)))
      Φ hx hT hΦ hderiv hΦT hΦ0
  have hfam := marked_family_summed_error_of_bounds (Finset.Icc 1 R)
    (fun r => (Finset.Icc 0 ⌊T * x⌋₊).filter (fun u => r ∣ u + 1))
    (representedArrayChoices P a) (fun u => Φ ((u : ℝ) / x))
    (representedArrayCoefficient W a)
    (fun t => markedWeightedModel Q (representedArraySelected t) θ)
    (fun t u => markedWeightedResidual Q (representedArraySelected t) θ u)
    (fun r => (x * ∫ t in Set.Ioc 0 T, Φ t) / (r : ℝ))
    (fun t => (∏ p ∈ representedArraySelected t, p : ℕ)) _ _ hterm
  dsimp only [Q, θ] at hfam
  simp_rw [← bandWeight_product_powers_eq_normalized_residual_sum P W a ha hdis] at hfam
  exact hfam

end ArtinMatthews
