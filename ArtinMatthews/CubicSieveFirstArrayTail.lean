module

public import ArtinMatthews.CubicSieveFirstArrayModel
public import ArtinMatthews.CubicSamplingArrayTruncation
public import ArtinMatthews.CubicSieveFirstArrayMass
public import ArtinMatthews.MarkedArrayReciprocalBounds
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Value and derivative errors of the original total-degree truncation. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

theorem cubicSieve_firstArrayTruncation_coefficients {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (V : J → ℝ) (g : ℕ → ℝ) (k : ℕ) :
    cubicSieveFirstArrayTruncationModel P V g k =
      ∑ t ∈ representedArrayChoices P (fun _ => 1),
        ∑ i ∈ markedWeightedIndices (univ.biUnion P) (representedArraySelected t) k,
          (representedArrayCoefficient V (fun _ => 1) t *
            markedWeightedCoefficient (representedArrayDamping univ P (fun _ => 1) (1 / 2)) i) *
          ∏ p ∈ representedArraySelected t ∪ i.2, g p := by
  unfold cubicSieveFirstArrayTruncationModel
  simp_rw [cubicSieve_selectedTruncation_eq_coefficients, mul_sum, mul_assoc]

theorem cubicSieve_firstArrayTruncation_tail {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (g : ℕ → ℝ)
    (hg : ∀ p ∈ univ.biUnion P, 0 ≤ g p ∧ g p ≤ 1 / (p : ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hmass : (∑ p ∈ univ.biUnion P, g p) ≤ M) (k : ℕ) :
    |cubicSieveFirstArrayTruncationModel P (fun j => bandReciprocalMass (P j)) g k -
      cubicSieveFirstArrayFullModel P (fun j => bandReciprocalMass (P j)) g| ≤
      2 * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k := by
  let V (j : J) := bandReciprocalMass (P j)
  let A := representedArrayChoices P (fun _ => 1)
  let c := representedArrayCoefficient V (fun _ => 1)
  let θ := representedArrayDamping univ P (fun _ => 1) (1 / 2)
  let B := 2 * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k
  have hθ (p : ℕ) (hp : p ∈ univ.biUnion P) : 0 ≤ θ p ∧ θ p ≤ 1 := by
    rw [show θ p = 1 / 2 from cubicSieve_firstArrayDamping_eq P hdis hp]
    norm_num
  change |(∑ t ∈ A, c t * _) - (∑ t ∈ A, c t * _)| ≤ B
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ t ∈ A, c t * ((∏ p ∈ representedArraySelected t, g p) * B) := by
      apply sum_le_sum
      intro t ht
      have hc : 0 ≤ c t := representedArrayCoefficient_nonneg _ (fun j => (hV j).le) _ t
      rw [abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left (cubicSieve_selectedTruncation_tail _ _
        (cubicSampling_selected_subset P (fun _ => 1) ht) θ g hM (fun p hp => (hg p hp).1) hθ hmass k) hc
    _ = (∑ t ∈ A, c t * ∏ p ∈ representedArraySelected t, g p) * B := by
      simp only [← mul_assoc, ← sum_mul]
    _ ≤ B := mul_le_of_le_one_left (by positivity)
      (cubicSieve_firstArray_selected_mass_le_one P hdis hV g hg)

theorem cubicSieve_firstArrayTruncationTangent_tail {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hdis : Pairwise fun i j => Disjoint (P i) (P j))
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) (g v : ℕ → ℝ)
    (hg : ∀ p ∈ univ.biUnion P, 0 ≤ g p ∧ g p ≤ 1 / (p : ℝ))
    {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hv : ∀ p ∈ univ.biUnion P, |v p| ≤ L * g p)
    (hmass : (∑ p ∈ univ.biUnion P, g p) ≤ M) (k : ℕ) :
    |cubicSieveFirstArrayTruncationTangent P (fun j => bandReciprocalMass (P j)) g v k -
      cubicSieveFirstArrayFullTangent P (fun j => bandReciprocalMass (P j)) g v| ≤
      2 * L * ((Fintype.card J : ℝ) + 1) * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k := by
  let V (j : J) := bandReciprocalMass (P j)
  let A := representedArrayChoices P (fun _ => 1)
  let c := representedArrayCoefficient V (fun _ => 1)
  let θ := representedArrayDamping univ P (fun _ => 1) (1 / 2)
  let B := 2 * L * ((Fintype.card J : ℝ) + 1) * Real.exp (8 * M) * (1 / 4 : ℝ) ^ k
  have hθ (p : ℕ) (hp : p ∈ univ.biUnion P) : 0 ≤ θ p ∧ θ p ≤ 1 := by
    rw [show θ p = 1 / 2 from cubicSieve_firstArrayDamping_eq P hdis hp]
    norm_num
  change |(∑ t ∈ A, c t * _) - (∑ t ∈ A, c t * _)| ≤ B
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ t ∈ A, c t * ((∏ p ∈ representedArraySelected t, g p) * B) := by
      apply sum_le_sum
      intro t ht
      have hc : 0 ≤ c t := representedArrayCoefficient_nonneg _ (fun j => (hV j).le) _ t
      have hS := cubicSampling_selected_subset P (fun _ => 1) ht
      have hP : 0 ≤ ∏ p ∈ representedArraySelected t, g p :=
        prod_nonneg (fun p hp => (hg p (hS hp)).1)
      rw [abs_mul, abs_of_nonneg hc]
      apply mul_le_mul_of_nonneg_left _ hc
      exact (cubicSieve_selectedTruncationTangent_tail _ _ hS θ g v hM hL
        (fun p hp => (hg p hp).1) hθ hv hmass k).trans
        (mul_le_mul_of_nonneg_left (by
          dsimp only [B]
          gcongr
          exact Nat.cast_le.mpr (cubicSieve_firstArray_selected_card t)) hP)
    _ = (∑ t ∈ A, c t * ∏ p ∈ representedArraySelected t, g p) * B := by
      simp only [← mul_assoc, ← sum_mul]
    _ ≤ B := mul_le_of_le_one_left (by positivity)
      (cubicSieve_firstArray_selected_mass_le_one P hdis hV g hg)

end ArtinMatthews
