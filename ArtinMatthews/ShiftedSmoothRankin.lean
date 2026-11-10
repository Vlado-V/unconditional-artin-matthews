module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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


set_option backward.privateInPublic true
@[expose] public section

/-! Rankin's bound for integers supported on an arbitrary finite prime set.
The proof uses the convergent finite Euler product, not a smooth-number estimate
as an additional hypothesis. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def shiftedNegativePower (ε : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ)^(-ε)
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

def shiftedSmoothSet (B : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 B).filter (fun n => n∈Nat.factoredNumbers P)

theorem shiftedSmooth_rankin (B : ℕ) (P : Finset ℕ) (ε : ℝ) (hε : 0<ε) :
    ((shiftedSmoothSet B P).card : ℝ) ≤
      (B : ℝ)^ε * ∏ p ∈ P with p.Prime, (1-(p : ℝ)^(-ε))⁻¹ := by
  let T : Finset (Nat.factoredNumbers P) := (Finset.Icc 1 B).subtype _
  have hlocal {p : ℕ} (hp : p.Prime) : ‖shiftedNegativePower ε p‖<1 := by
    change ‖(p : ℝ)^(-ε)‖<1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    hlocal P).2
  have hcount : ((shiftedSmoothSet B P).card : ℝ) = ∑ _n ∈ T, (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    exact (Finset.card_subtype _ _).symm
  rw [hcount]
  calc
    _ ≤ ∑ n ∈ T, (B : ℝ)^ε*(n.val : ℝ)^(-ε) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnb := Finset.mem_Icc.mp (Finset.mem_subtype.mp hn)
      have hn0 : (0 : ℝ)<n.val := by exact_mod_cast hnb.1
      have hnB : (n.val : ℝ)≤B := by exact_mod_cast hnb.2
      have hp : (n.val : ℝ)^ε≤(B : ℝ)^ε := Real.rpow_le_rpow hn0.le hnB hε.le
      rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
      exact (one_le_div (Real.rpow_pos_of_pos hn0 ε)).mpr hp
    _ = (B : ℝ)^ε*∑ n ∈ T, shiftedNegativePower ε n.val := by
      rw [Finset.mul_sum]
      rfl
    _ ≤ (B : ℝ)^ε*∑' n : Nat.factoredNumbers P, shiftedNegativePower ε n.val := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg B) _)
      exact Summable.sum_le_tsum T (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n.val) _) hs.summable
    _ = _ := by rw [hs.tsum_eq]; rfl

end
end ArtinMatthews
