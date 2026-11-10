module

public import ArtinMatthews.CubicSieveModelTangent
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
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Relative value and tangent bounds on one genuine divisor-density block.
The cap 3/4 includes the prime 2. -/

noncomputable section
namespace ArtinMatthews

open Finset OAI.Erdos970.NumberTheoryLean
open scoped BigOperators

theorem cubicSieve_blockEuler_lower (P : Finset ℕ) (g : ℕ → ℝ) {A : ℝ}
    (hg : ∀ p ∈ P, 0 ≤ g p) (hcap : ∀ p ∈ P, g p ≤ 3 / 4)
    (hsum : (∑ p ∈ P, g p) ≤ A) :
    Real.exp (-4 * A) ≤ ∏ p ∈ P, (1 - g p) := by
  have hpoint (p : ℕ) (hp : p ∈ P) : Real.exp (-4 * g p) ≤ 1 - g p := by
    have hpos : 0 < 1 - g p := by linarith only [hcap p hp]
    have hinv : (1 - g p)⁻¹ ≤ 1 + 4 * g p := by
      apply (inv_le_iff_one_le_mul₀ hpos).mpr
      nlinarith only [mul_nonneg (hg p hp) (show 0 ≤ 3 - 4 * g p by linarith only [hcap p hp])]
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    exact (Real.le_log_iff_exp_le hpos).mp (by linarith only [hinv, hlog])
  calc
    _ ≤ Real.exp (-4 * ∑ p ∈ P, g p) := Real.exp_le_exp.mpr (by linarith only [hsum])
    _ = ∏ p ∈ P, Real.exp (-4 * g p) := by rw [mul_sum, Real.exp_sum]
    _ ≤ _ := prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) hpoint

theorem cubicSieve_elementarySum_geometric (P : Finset ℕ) (g : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hg : ∀ p ∈ P, 0 ≤ g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    BonferroniDensity.elementarySum P g k ≤ Real.exp (8 * A) * (1 / 8 : ℝ) ^ k := by
  calc
    _ ≤ A ^ k / k.factorial := BonferroniDensity.elementarySum_le_pow_div_factorial P g hg hA hsum k
    _ = ((8 * A) ^ k / k.factorial) / (8 : ℝ) ^ k := by
      rw [mul_pow]
      field_simp
    _ ≤ Real.exp (8 * A) / (8 : ℝ) ^ k :=
      div_le_div_of_nonneg_right (Real.pow_div_factorial_le_exp _ (by positivity) k) (by positivity)
    _ = _ := by rw [div_pow, one_pow]; ring

theorem cubicSieve_elementaryTangent_geometric (P : Finset ℕ) (g v : ℕ → ℝ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hv : ∀ p ∈ P, |v p| ≤ L * g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |cubicSieveElementaryTangent P g v k| ≤ L * Real.exp (8 * A) * (1 / 4 : ℝ) ^ k := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (show k < 2 ^ k from Nat.lt_two_pow_self).le
  have hE := cubicSieve_elementarySum_geometric P g hA hg hsum k
  calc
    _ ≤ (k : ℝ) * L * BonferroniDensity.elementarySum P g k :=
      cubicSieve_elementaryTangent_abs_le P g v L hg hv k
    _ ≤ (2 : ℝ) ^ k * L * (Real.exp (8 * A) * (1 / 8 : ℝ) ^ k) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hk hL) hE
        (BonferroniDensity.elementarySum_nonneg P g hg k) (by positivity)
    _ = L * Real.exp (8 * A) * ((2 : ℝ) ^ k * (1 / 8 : ℝ) ^ k) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem cubicSieve_polynomialTangent_bound (P : Finset ℕ) (g v : ℕ → ℝ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p)
    (hv : ∀ p ∈ P, |v p| ≤ L * g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |cubicSievePolynomialTangent k P g v| ≤ 2 * L * Real.exp (8 * A) := by
  unfold cubicSievePolynomialTangent
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ range (k + 1), L * Real.exp (8 * A) * (1 / 2 : ℝ) ^ j := by
      apply sum_le_sum
      intro j _
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact (cubicSieve_elementaryTangent_geometric P g v hA hL hg hv hsum j).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) j) (by positivity))
    _ = L * Real.exp (8 * A) * ∑ j ∈ range (k + 1), (1 / 2 : ℝ) ^ j := (mul_sum _ _ _).symm
    _ ≤ _ := (mul_le_mul_of_nonneg_left (sum_geometric_two_le (k + 1)) (by positivity)).trans_eq (by ring)

private theorem cubicSieve_div_exp_bound {A E y K : ℝ}
    (hE : Real.exp (-4 * A) ≤ E) (hK : 0 ≤ K) (hy : y ≤ Real.exp (8 * A) * K) :
    y / E ≤ Real.exp (12 * A) * K := by
  have hpos : 0 < E := (Real.exp_pos _).trans_le hE
  calc
    _ ≤ (Real.exp (8 * A) * K) / E := div_le_div_of_nonneg_right hy hpos.le
    _ ≤ (Real.exp (8 * A) * K) / Real.exp (-4 * A) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hE
    _ = _ := by
      have h : Real.exp (8 * A) / Real.exp (-4 * A) = Real.exp (12 * A) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      rw [← h]
      ring

theorem cubicSieve_elementary_relative_bound (P : Finset ℕ) (g : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hg : ∀ p ∈ P, 0 ≤ g p) (hcap : ∀ p ∈ P, g p ≤ 3 / 4)
    (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    BonferroniDensity.elementarySum P g k / (∏ p ∈ P, (1 - g p)) ≤
      Real.exp (12 * A) * (1 / 4 : ℝ) ^ k := by
  apply cubicSieve_div_exp_bound (cubicSieve_blockEuler_lower P g hg hcap hsum) (by positivity)
  exact (cubicSieve_elementarySum_geometric P g hA hg hsum k).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) k) (by positivity))

theorem cubicSieve_elementaryTangent_relative_bound (P : Finset ℕ) (g v : ℕ → ℝ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p) (hcap : ∀ p ∈ P, g p ≤ 3 / 4)
    (hv : ∀ p ∈ P, |v p| ≤ L * g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |cubicSieveElementaryTangent P g v k| / (∏ p ∈ P, (1 - g p)) ≤
      L * Real.exp (12 * A) * (1 / 4 : ℝ) ^ k := by
  rw [mul_comm L (Real.exp (12 * A)), mul_assoc]
  apply cubicSieve_div_exp_bound (cubicSieve_blockEuler_lower P g hg hcap hsum) (by positivity)
  exact (cubicSieve_elementaryTangent_geometric P g v hA hL hg hv hsum k).trans_eq (by ring)

theorem cubicSieve_polynomialTangent_relative_bound (P : Finset ℕ) (g v : ℕ → ℝ) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hg : ∀ p ∈ P, 0 ≤ g p) (hcap : ∀ p ∈ P, g p ≤ 3 / 4)
    (hv : ∀ p ∈ P, |v p| ≤ L * g p) (hsum : (∑ p ∈ P, g p) ≤ A) (k : ℕ) :
    |cubicSievePolynomialTangent k P g v| / (∏ p ∈ P, (1 - g p)) ≤
      2 * L * Real.exp (12 * A) := by
  rw [mul_comm (2 * L) (Real.exp (12 * A))]
  apply cubicSieve_div_exp_bound (cubicSieve_blockEuler_lower P g hg hcap hsum) (by positivity)
  exact (cubicSieve_polynomialTangent_bound P g v hA hL hg hv hsum k).trans_eq (by ring)

theorem cubicSieve_upperPolynomial_relative_bound (P : Finset ℕ) (g : ℕ → ℝ) {A : ℝ}
    (hA : 0 ≤ A) (hg : ∀ p ∈ P, 0 ≤ g p) (hcap : ∀ p ∈ P, g p ≤ 3 / 4)
    (hsum : (∑ p ∈ P, g p) ≤ A) (m : ℕ) :
    0 ≤ BonferroniDensity.densityPolynomial (2 * m) P g / (∏ p ∈ P, (1 - g p)) ∧
      BonferroniDensity.densityPolynomial (2 * m) P g / (∏ p ∈ P, (1 - g p)) ≤
        1 + Real.exp (12 * A) * (1 / 4 : ℝ) ^ (2 * m + 1) := by
  let E := ∏ p ∈ P, (1 - g p)
  have hE : 0 < E := (Real.exp_pos _).trans_le (cubicSieve_blockEuler_lower P g hg hcap hsum)
  have hB := BonferroniDensity.densityPolynomial_bounds P g hg
    (fun p hp => (hcap p hp).trans (by norm_num)) m
  have hgap := BonferroniDensity.densityPolynomial_gap m P g
  have hU : BonferroniDensity.densityPolynomial (2 * m) P g ≤
      E + BonferroniDensity.elementarySum P g (2 * m + 1) := by
    change BonferroniDensity.densityPolynomial (2 * m) P g ≤
      (∏ p ∈ P, (1 - g p)) + BonferroniDensity.elementarySum P g (2 * m + 1)
    linarith only [hB.1, hgap]
  refine ⟨div_nonneg (hE.le.trans hB.2) hE.le, ?_⟩
  exact (div_le_div_of_nonneg_right hU hE.le).trans (by
    rw [add_div, div_self hE.ne']
    exact add_le_add le_rfl (cubicSieve_elementary_relative_bound P g hA hg hcap hsum _))

end ArtinMatthews
