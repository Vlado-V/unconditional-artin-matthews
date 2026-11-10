module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact survivor fractions for the symmetric product-space probe
projection, with a uniform contraction as the number of probes grows. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealProbe_prod_one_sub_lower {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [sum_insert hi, prod_insert hi]
    have hai := ha i (mem_insert_self i s)
    have has : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (mem_insert_of_mem hj)
    have hs := sum_nonneg (fun j hj => (has j hj).1)
    have hmul := mul_le_mul_of_nonneg_left (ih has) (sub_nonneg.mpr hai.2)
    nlinarith [mul_nonneg hai.1 hs]

theorem idealProbe_descFactorial_cast {M r : ℕ} (hr : r ≤ M) :
    (M.descFactorial r : ℝ) = (M.factorial : ℝ) / (M-r).factorial := by
  apply (eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (M-r)))).mpr
  rw [← Nat.cast_mul, Nat.mul_comm, Nat.factorial_mul_descFactorial hr]

theorem idealProbe_descFactorial_half {M r : ℕ} (hM : 0 < M) (hr : r ≤ M)
    (hlarge : r * (r-1) ≤ M) :
    (M : ℝ)^r ≤ 2 * (M.descFactorial r : ℝ) := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hMi (i : ℕ) (hi : i ∈ range r) : i ≤ M := (mem_range.mp hi).le.trans hr
  have hprod : (M.descFactorial r : ℝ) =
      (M : ℝ)^r * ∏ i ∈ range r, (1 - (i : ℝ)/M) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hterm (i : ℕ) (hi : i ∈ range r) : ((M-i : ℕ) : ℝ) = M * (1 - (i : ℝ)/M) := by
      rw [Nat.cast_sub (hMi i hi)]
      field_simp
    rw [prod_congr rfl hterm, prod_mul_distrib]
    simp
  have hsum : (∑ i ∈ range r, (i : ℝ)/M) ≤ 1/2 := by
    rw [← sum_div]
    have hs := Finset.sum_range_id_mul_two r
    have hs' := congrArg (fun n : ℕ => (n : ℝ)) hs
    push_cast at hs'
    have hl : (r : ℝ) * ((r-1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hlarge
    apply (div_le_iff₀ (Nat.cast_pos.mpr hM)).mpr
    nlinarith
  have hprod_lower := idealProbe_prod_one_sub_lower (range r) (fun i => (i : ℝ)/M)
    (fun i hi => ⟨div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg M),
      (div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr (hMi i hi))⟩)
  rw [hprod]
  have hp : 0 ≤ (M : ℝ)^r := pow_nonneg (Nat.cast_nonneg M) r
  nlinarith [mul_le_mul_of_nonneg_left hprod_lower hp]

def idealProbeSurvivorFraction (M m ell j : ℕ) : ℝ :=
  if m ≤ j ∧ j+ell ≤ M then
    ((M-m-ell).choose (j-m) : ℝ) / M.choose j else 0

theorem idealProbeSurvivorFraction_eq {M m ell j : ℕ}
    (hm : m ≤ j) (hj : j+ell ≤ M) :
    idealProbeSurvivorFraction M m ell j =
      (j.descFactorial m : ℝ) * ((M-j).descFactorial ell : ℝ) /
        (M.descFactorial (m+ell) : ℝ) := by
  have hjM : j ≤ M := by omega
  have hmell : m+ell ≤ M := by omega
  have hell : ell ≤ M-j := by omega
  have hnum : j-m ≤ M-m-ell := by omega
  have hsub : M-m-ell-(j-m) = M-j-ell := by omega
  have hsum : M-(m+ell) = M-m-ell := by omega
  rw [idealProbeSurvivorFraction, ite_eq_left ⟨hm,hj⟩,
    Nat.cast_choose ℝ hnum, Nat.cast_choose ℝ hjM,
    idealProbe_descFactorial_cast hm, idealProbe_descFactorial_cast hell,
    idealProbe_descFactorial_cast hmell, hsub, hsum]
  have hn (n : ℕ) : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp

theorem idealProbe_binomial_peak {m : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    t^m * (1-t) ≤ 1/(m+1 : ℕ) := by
  have hs := add_pow t (1-t) (m+1)
  have hterm : (m+1 : ℝ) * (t^m * (1-t)) ≤ (t+(1-t))^(m+1) := by
    rw [hs]
    have h := single_le_sum (f := fun i => (t^i * (1-t)^(m+1-i)) * ((m+1).choose i : ℝ))
      (fun i _ => mul_nonneg (mul_nonneg (pow_nonneg ht i) (pow_nonneg (sub_nonneg.mpr ht1) _))
        (Nat.cast_nonneg _)) (mem_range.mpr (show m < m+1+1 by omega))
    simpa only [Nat.add_sub_cancel_left, pow_one, Nat.choose_succ_self_right, Nat.cast_add,
      Nat.cast_one, mul_comm (m+1 : ℝ)] using h
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (m+1 : ℕ))).mpr
  have he : t+(1-t)=1 := by ring
  rw [he, one_pow] at hterm
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hterm

theorem idealProbeSurvivorFraction_le {M m ell j : ℕ} (hM : 0 < M)
    (hm : 1 ≤ m) (hell : 1 ≤ ell) (hlarge : (m+ell)*(m+ell-1) ≤ M) :
    idealProbeSurvivorFraction M m ell j ≤ 2/(m+1 : ℕ) := by
  by_cases hvalid : m ≤ j ∧ j+ell ≤ M
  · have hjM : j ≤ M := by omega
    have hr : m+ell ≤ M := by
      have htwo : 2 ≤ m+ell := by omega
      nlinarith
    rw [idealProbeSurvivorFraction_eq hvalid.1 hvalid.2]
    have hd : 0 < (M.descFactorial (m+ell) : ℝ) :=
      Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hr)
    have hden := idealProbe_descFactorial_half hM hr hlarge
    have hjpow : (j.descFactorial m : ℝ) ≤ (j : ℝ)^m := by exact_mod_cast Nat.descFactorial_le_pow j m
    have hmpow : ((M-j).descFactorial ell : ℝ) ≤ ((M-j : ℕ) : ℝ)^ell := by
      exact_mod_cast Nat.descFactorial_le_pow (M-j) ell
    let t : ℝ := (j : ℝ)/M
    have ht : 0 ≤ t := div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg M)
    have ht1 : t ≤ 1 := (div_le_one (Nat.cast_pos.mpr hM)).mpr (Nat.cast_le.mpr hjM)
    have htail : (1-t)^ell ≤ 1-t :=
      pow_le_of_le_one (sub_nonneg.mpr ht1) (by linarith) (by omega : ell ≠ 0)
    have hpeak := (mul_le_mul_of_nonneg_left htail (pow_nonneg ht m)).trans (idealProbe_binomial_peak ht ht1)
    have hnorm : (j : ℝ)^m * ((M-j : ℕ) : ℝ)^ell =
        (t^m * (1-t)^ell) * (M : ℝ)^(m+ell) := by
      rw [Nat.cast_sub hjM, pow_add]
      dsimp [t]
      rw [show 1-(j : ℝ)/M = ((M : ℝ)-j)/M by field_simp]
      simp only [div_pow]
      field_simp
    have hnum : (j.descFactorial m : ℝ) * ((M-j).descFactorial ell : ℝ) ≤
        (M : ℝ)^(m+ell)/(m+1 : ℕ) := by
      calc
        _ ≤ (j : ℝ)^m * ((M-j : ℕ) : ℝ)^ell :=
          mul_le_mul hjpow hmpow (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg j) m)
        _ = _ := hnorm
        _ ≤ (1/(m+1 : ℕ)) * (M : ℝ)^(m+ell) :=
          mul_le_mul_of_nonneg_right hpeak (pow_nonneg (Nat.cast_nonneg M) (m+ell))
        _ = _ := by ring
    apply (div_le_iff₀ hd).mpr
    have hb : 0 ≤ (1 : ℝ)/(m+1 : ℕ) := by positivity
    have hs := mul_le_mul_of_nonneg_right hden hb
    apply hnum.trans
    calc
      _ = (M : ℝ)^(m+ell) * (1/(m+1 : ℕ)) := by ring
      _ ≤ _ := hs
      _ = _ := by ring
  · rw [idealProbeSurvivorFraction, ite_eq_right hvalid]
    positivity

end
end ArtinMatthews
