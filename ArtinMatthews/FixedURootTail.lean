module

public import ArtinMatthews.FixedURootEuler
public import ArtinMatthews.ReciprocalTail
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
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


set_option backward.privateInPublic true
@[expose] public section

/-! The actual reciprocal-square tail estimate used to replace the finite
Möbius main coefficient by its convergent Euler coefficient. -/
namespace ArtinMatthews
open scoped BigOperators

/-- A sequence bounded by `1/n²` has truncation error at most `1/N`.
The proof is finite telescoping followed by absolute summation. -/
theorem reciprocal_square_truncation_error {f : ℕ → ℝ}
    (hf : ∀ n, |f n| ≤ 1/(n : ℝ)^2) (N : ℕ) (hN : 0 < N) :
    |(∑' n, f n) - ∑ n ∈ Finset.Icc 1 N, f n| ≤ 1/(N : ℝ) := by
  classical
  have hnorm : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
      simpa only [Real.norm_eq_abs] using hf n)
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hf0 : f 0 = 0 := by
    have hh := hf 0
    simpa using hh
  let R := Finset.range (N+1)
  have htail : ∀ n : {n : ℕ // n ∉ R}, N < (n : ℕ) := by
    intro n
    have hn := n.property
    simp only [R,Finset.mem_range] at hn
    omega
  have hfinite : ∀ P : Finset {n : ℕ // n ∉ R},
      (∑ n ∈ P, ‖f n‖) ≤ 1/(N : ℝ) := by
    intro P
    let Q := P.image (fun n : {n : ℕ // n ∉ R} => n.val)
    have hQ : ∀ q ∈ Q, N < q := by
      intro q hq
      obtain ⟨n,_,rfl⟩ := Finset.mem_image.mp hq
      exact htail n
    calc
      _ ≤ ∑ n ∈ P, 1/((n : ℕ) : ℝ)^2 := Finset.sum_le_sum (fun n _ => by
        simpa only [Real.norm_eq_abs] using hf n)
      _ ≤ ∑ n ∈ P, 1/(((n : ℕ) : ℝ)*(((n : ℕ) : ℝ)-1)) := by
        apply Finset.sum_le_sum
        intro n _
        have hn : (1 : ℝ) < (n : ℕ) := by exact_mod_cast (show 1 < (n : ℕ) by have := htail n; omega)
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      _ = ∑ n ∈ Q, 1/((n : ℝ)*((n : ℝ)-1)) := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Subtype.ext hab
      _ ≤ 1/(N : ℝ) := sum_reciprocal_tail_le Q N hN hQ
  have hbound : (∑' n : {n : ℕ // n ∉ R}, ‖f n‖) ≤ 1/(N : ℝ) :=
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hfinite
  have he : R = insert 0 (Finset.Icc 1 N) := by
    ext n
    simp only [R,Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  have hsum : (∑ n ∈ R, f n) = ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [he,Finset.sum_insert (by simp),hf0,zero_add]
  rw [← hsum,← hnorm.of_norm.sum_add_tsum_subtype_compl R,add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm (hnorm.subtype _)).trans hbound


/-- The actual Möbius coefficient satisfies the reciprocal-square comparison. -/
theorem fixedURootEulerTerm_abs_le (S n : ℕ) :
    |fixedURootEulerTerm S n| ≤ 1/(n : ℝ)^2 := by
  have hmu : |(ArithmeticFunction.moebius n : ℤ)| ≤ 1 :=
    ArithmeticFunction.abs_moebius_le_one
  have hmuR : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by exact_mod_cast hmu
  by_cases hn : n.Coprime S
  · rw [fixedURootEulerTerm,ite_eq_left hn,abs_div,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ)^2 from sq_nonneg _)]
    exact div_le_div_of_nonneg_right hmuR (sq_nonneg _)
  · rw [fixedURootEulerTerm,ite_eq_right hn,abs_zero]
    positivity

/-- Replacing the finite main coefficient by the genuine convergent Euler
constant costs at most `1/N`, uniformly in the residue modulus. -/
theorem fixedURootEuler_truncation_error (S N : ℕ) (hN : 0 < N) :
    |(∑' n, fixedURootEulerTerm S n) -
      ∑ n ∈ Finset.Icc 1 N, fixedURootEulerTerm S n| ≤ 1/(N : ℝ) :=
  reciprocal_square_truncation_error (fixedURootEulerTerm_abs_le S) N hN

end ArtinMatthews
