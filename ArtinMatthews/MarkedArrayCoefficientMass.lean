module

public import ArtinMatthews.MarkedArrayEulerModel
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

/-! The number-weighted coefficient mass controls rounding errors. Its
large prime-choice factor is kept separate from reciprocal model mass. -/

namespace ArtinMatthews

open scoped BigOperators

/-- Distinct positive integers bounded by `Z` have cardinality at most `Z`. -/
theorem marked_prime_set_card_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {Z : ℝ} (hZ : 0 ≤ Z) (hbound : ∀ p ∈ P, (p : ℝ) ≤ Z) : (P.card : ℝ) ≤ Z := by
  have hsub : P ⊆ Finset.Icc 1 ⌊Z⌋₊ := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).pos, (Nat.le_floor_iff hZ).mpr (hbound p hp)⟩
  have hcard : P.card ≤ ⌊Z⌋₊ := by simpa using Finset.card_le_card hsub
  exact (by exact_mod_cast hcard : (P.card : ℝ) ≤ ⌊Z⌋₊).trans (Nat.floor_le hZ)

theorem representedArrayCoefficient_nonneg_for_mass {ι : Type*} [Fintype ι]
    (W : ι → ℝ) (a : ι → ℕ) (hW : ∀ i, 0 ≤ W i)
    (t : (i : ι) → Fin (a i) → ℕ) : 0 ≤ representedArrayCoefficient W a t := by
  unfold representedArrayCoefficient
  apply div_nonneg
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg (by norm_num) _)
  · exact Finset.prod_nonneg (fun i _ => pow_nonneg (hW i) _)

/-- Exact tuple counting provides the unnormalized coefficient bound. -/
theorem representedArrayCoefficient_mass_le_product {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ) (hW : ∀ i, 0 < W i) :
    (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) ≤
      ∏ i, ((P i).card : ℝ) ^ a i / W i ^ a i := by
  classical
  have hden : 0 < ∏ i, W i ^ a i := Finset.prod_pos (fun i _ => pow_pos (hW i) _)
  calc
    _ = (∑ t ∈ representedArrayChoices P a,
        ∏ i, (1 / 2 : ℝ) ^ (a i * ((representedChoiceSet (t i)).card - 1))) /
        (∏ i, W i ^ a i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro t _
      rw [abs_of_nonneg (representedArrayCoefficient_nonneg_for_mass W a (fun i => (hW i).le) t)]
      rfl
    _ ≤ (∑ _t ∈ representedArrayChoices P a, (1 : ℝ)) / (∏ i, W i ^ a i) := by
      apply div_le_div_of_nonneg_right _ hden.le
      apply Finset.sum_le_sum
      intro t _
      exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (by norm_num) _)
        (fun i _ => pow_le_one₀ (by norm_num) (by norm_num))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, representedArrayChoices,
        Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Nat.cast_prod, Nat.cast_pow, Finset.prod_div_distrib]

/-- Uniform lower normalizers and upper band cardinalities give an explicit
power bound for all represented tuple coefficients. -/
theorem representedArrayCoefficient_mass_le {ι : Type*} [Fintype ι]
    (P : ι → Finset ℕ) (W : ι → ℝ) (a : ι → ℕ)
    {v Z : ℝ} (hv : 0 < v) (hZ : 0 ≤ Z) (hW : ∀ i, v ≤ W i)
    (hcard : ∀ i, ((P i).card : ℝ) ≤ Z) :
    (∑ t ∈ representedArrayChoices P a, |representedArrayCoefficient W a t|) ≤
      (Z / v) ^ (∑ i, a i) := by
  apply (representedArrayCoefficient_mass_le_product P W a (fun i => hv.trans_le (hW i))).trans
  calc
    _ = ∏ i, (((P i).card : ℝ) / W i) ^ a i := by simp only [div_pow]
    _ ≤ ∏ i, (Z / v) ^ a i := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (div_nonneg (Nat.cast_nonneg _) (hv.trans_le (hW i)).le) _
      · intro i _
        apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (hv.trans_le (hW i)).le)
        exact div_le_div₀ hZ (hcard i) hv (hW i)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

end ArtinMatthews
