module

public import ArtinMatthews.MarkedProgressionWeightedModel
public import ArtinMatthews.MarkedProgressionComparison
public import ArtinMatthews.MarkedProgressionUnrestricted


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite smooth progression estimate for a selected weighted
residual. All remaining terms are explicit coefficient, local, and positive
Bonferroni-tail masses; no progression estimate is an input. -/

namespace ArtinMatthews

open MeasureTheory
open scoped BigOperators

noncomputable def markedWeightedCoefficientMass (P S : Finset ℕ) (θ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ markedWeightedIndices P S k, |markedWeightedCoefficient θ i|

noncomputable def markedWeightedLocalMass (P S : Finset ℕ) (θ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ markedWeightedIndices P S k,
    (|markedWeightedCoefficient θ i| / (markedWeightedDivisor S i : ℝ)) *
      ∑ p ∈ (markedWeightedDivisor S i).primeFactors, 1 / (p : ℝ)

noncomputable def markedWeightedTailCoefficientMass (P S : Finset ℕ) (θ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ T ∈ (P \ S).powersetCard k, ∏ p ∈ T, θ p

/-- Explicit finite summed remainder, obtained from the exact CRT count,
partial summation, and the positive Bonferroni omitted tail. -/
theorem marked_weighted_residual_summed_error (P S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hS : S ⊆ P) (θ : ℕ → ℝ)
    (hθ : ∀ p ∈ P, 0 ≤ θ p ∧ θ p ≤ 1) (m R : ℕ)
    (f : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (hf : Differentiable ℝ f)
    (hderiv : Continuous (deriv f)) (hfT : f T = 0) (hf0 : ∀ t, 0 ≤ f t) :
    (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ (Finset.Icc 0 ⌊T⌋₊).filter (fun u => r ∣ u + 1),
          f u * markedWeightedResidual P S θ u) -
        ((∫ t in Set.Ioc 0 T, f t) / (r : ℝ)) * markedWeightedModel P S θ|) ≤
      (R : ℝ) * (3 * ∫ t in Set.Ioc 0 T, |deriv f t|) *
        (markedWeightedCoefficientMass P S θ (2 * m) +
          markedWeightedTailCoefficientMass P S θ (2 * m + 1)) +
      ((∫ t in Set.Ioc 0 T, f t) * (harmonic R : ℝ)) *
        (markedWeightedLocalMass P S θ (2 * m) +
          2 * markedWeightedTailModel P S θ (2 * m + 1)) := by
  classical
  let I : ℝ := ∫ t in Set.Ioc 0 T, f t
  let V : ℝ := 3 * ∫ t in Set.Ioc 0 T, |deriv f t|
  let J := markedWeightedIndices P S (2 * m)
  let U := Finset.Icc 0 ⌊T⌋₊
  let A := markedWeightedTruncation P S θ (2 * m)
  let D := markedWeightedTail P S θ (2 * m + 1)
  let MA : ℝ := ∑ i ∈ J, markedWeightedCoefficient θ i / (markedWeightedDivisor S i : ℝ)
  let MT := markedWeightedTailModel P S θ (2 * m + 1)
  have hI : 0 ≤ I := integral_nonneg hf0
  have hpoly := marked_indexed_polynomial_unrestricted_error R J (markedWeightedDivisor S)
    (markedWeightedCoefficient θ) (fun _ hi => markedWeightedDivisor_pos P S hP hS hi)
    f hT hf hderiv hfT
  dsimp only [J] at hpoly
  simp_rw [← markedWeightedTruncation_eq_polynomial] at hpoly
  change (∑ r ∈ Finset.Icc 1 R,
      |(∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * A u) - (I / r) * MA|) ≤
    (R : ℝ) * V * markedWeightedCoefficientMass P S θ (2 * m) +
      |I| * (harmonic R : ℝ) * markedWeightedLocalMass P S θ (2 * m) at hpoly
  rw [abs_of_nonneg hI] at hpoly
  have hdiv (Q : Finset ℕ) (hQ : Q ∈ (P \ S).powersetCard (2 * m + 1)) :
      0 < ∏ p ∈ S ∪ Q, p := by
    apply Finset.prod_pos
    intro p hp
    exact (hP p (Finset.mem_union.mp hp |>.elim (fun h => hS h)
      (fun h => (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hQ).1 h)).1))).pos
  have hcoef (Q : Finset ℕ) (hQ : Q ∈ (P \ S).powersetCard (2 * m + 1)) :
      0 ≤ ∏ p ∈ Q, θ p := by
    apply Finset.prod_nonneg
    intro p hp
    exact (hθ p (Finset.mem_sdiff.mp ((Finset.mem_powersetCard.mp hQ).1 hp)).1).1
  have htail := marked_positive_polynomial_summed_upper R ((P \ S).powersetCard (2 * m + 1))
    (fun Q => ∏ p ∈ S ∪ Q, p) (fun Q => ∏ p ∈ Q, θ p) hdiv hcoef
    f hT hf hderiv hfT hI
  change (∑ r ∈ Finset.Icc 1 R, ∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * D u) ≤
    (I * (harmonic R : ℝ)) * MT +
      (R : ℝ) * V * markedWeightedTailCoefficientMass P S θ (2 * m + 1) at htail
  have hmodel : |markedWeightedModel P S θ - MA| ≤ MT :=
    markedWeightedModel_truncation_error P S hP θ hθ m
  have happ (u : ℕ) : |markedWeightedResidual P S θ u - A u| ≤ D u := by
    have h := markedWeightedTruncation_error P S hP hS θ hθ m u
    rw [abs_sub_comm, abs_of_nonneg h.1]
    exact h.2
  have hcomp (r : ℕ) :
      |(∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * markedWeightedResidual P S θ u) -
          (I / r) * markedWeightedModel P S θ| ≤
        |(∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * A u) - (I / r) * MA| +
          (∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * D u) + (I / r) * MT := by
    have h := marked_sum_comparison (U.filter (fun u => r ∣ u + 1)) (fun u => f u)
      (markedWeightedResidual P S θ) A D (fun u _ => hf0 u) (fun u _ => happ u)
      (c := I / r) hmodel
    rwa [abs_of_nonneg (div_nonneg hI (Nat.cast_nonneg r))] at h
  have hsum : (∑ r ∈ Finset.Icc 1 R, (I / (r : ℝ)) * MT) =
      (I * (harmonic R : ℝ)) * MT := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← reciprocal_Icc_eq_harmonic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R,
        (|(∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * A u) - (I / r) * MA| +
          (∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * D u) + (I / r) * MT) :=
      Finset.sum_le_sum (fun r _ => hcomp r)
    _ = (∑ r ∈ Finset.Icc 1 R,
        |(∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * A u) - (I / r) * MA|) +
        (∑ r ∈ Finset.Icc 1 R, ∑ u ∈ U.filter (fun u => r ∣ u + 1), f u * D u) +
        (I * (harmonic R : ℝ)) * MT := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsum]
    _ ≤ ((R : ℝ) * V * markedWeightedCoefficientMass P S θ (2 * m) +
          I * (harmonic R : ℝ) * markedWeightedLocalMass P S θ (2 * m)) +
        ((I * (harmonic R : ℝ)) * MT +
          (R : ℝ) * V * markedWeightedTailCoefficientMass P S θ (2 * m + 1)) +
        (I * (harmonic R : ℝ)) * MT := add_le_add (add_le_add hpoly htail) le_rfl
    _ = _ := by dsimp [I, V, MT]; ring

end ArtinMatthews
