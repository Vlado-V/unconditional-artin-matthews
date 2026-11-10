module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# The Euler constant for the fixed-u average

The principal Dirichlet character deletes exactly the primes dividing the
fixed modulus. Its L-series and its Möbius twist are multiplicative inverses
in the half-plane of absolute convergence. At `s = 2`, this gives the actual
absolutely convergent real series needed by the root average.
-/

namespace ArtinMatthews

open scoped BigOperators ArithmeticFunction.Moebius LSeries.notation

/-- The real summand in the root-average Euler constant. -/
noncomputable def fixedURootEulerTerm (S n : ℕ) : ℝ :=
  if n.Coprime S then (μ n : ℝ) / (n : ℝ) ^ 2 else 0

theorem fixedURootEulerTerm_summable (S : ℕ) : Summable (fixedURootEulerTerm S) := by
  apply (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).of_norm_bounded
  intro n
  have hmu : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
  by_cases hn : n.Coprime S
  · rw [fixedURootEulerTerm, ite_eq_left hn]
    simpa only [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (sq_nonneg (n : ℝ))] using
      div_le_div_of_nonneg_right hmu (sq_nonneg (n : ℝ))
  · rw [fixedURootEulerTerm, ite_eq_right hn, norm_zero]
    positivity

theorem fixedU_principal_character_apply (S n : ℕ) :
    (1 : DirichletCharacter ℂ S) n = if n.Coprime S then 1 else 0 := by
  by_cases hn : n.Coprime S
  · rw [ite_eq_left hn]
    exact MulChar.one_apply ((ZMod.isUnit_iff_coprime n S).mpr hn)
  · rw [ite_eq_right hn]
    exact MulChar.map_nonunit _ (fun hu => hn ((ZMod.isUnit_iff_coprime n S).mp hu))

/-- Principal-character Euler factor deletion, specialized to the square-summable point. -/
theorem fixedU_principal_LSeries_two (S : ℕ) [NeZero S] :
    LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) n) 2 =
      riemannZeta 2 * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℂ) ^ 2) := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h := DirichletCharacter.LSeries_changeLevel (one_dvd S)
    (1 : DirichletCharacter ℂ 1) hs
  rw [DirichletCharacter.changeLevel_one, DirichletCharacter.modOne_eq_one,
    LSeries_one_eq_riemannZeta hs] at h
  have hp (p : ℕ) : (1 : DirichletCharacter ℂ 1) p = 1 :=
    MulChar.one_apply (isUnit_of_subsingleton _)
  simpa only [hp, one_mul,
    Complex.cpow_neg, Complex.cpow_two, one_div] using h

/-- The absolutely convergent complex Möbius series with the fixed prime
factors deleted is the reciprocal principal-character L-series. -/
theorem fixedU_complex_moebius_sum_two (S : ℕ) [NeZero S] :
    (∑' n : ℕ, if n.Coprime S then (μ n : ℂ) / (n : ℂ) ^ 2 else 0) =
      (riemannZeta 2)⁻¹ * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℂ) ^ 2)⁻¹ := by
  let χ : DirichletCharacter ℂ S := 1
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  change LSeries (fun n : ℕ => χ n) 2 *
    LSeries (fun n : ℕ => χ n * (μ n : ℂ)) 2 = 1 at hmul
  have hne := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
  have hinv : LSeries (fun n : ℕ => χ n * (μ n : ℂ)) 2 =
      (LSeries (fun n : ℕ => χ n) 2)⁻¹ := by
    apply mul_left_cancel₀ hne
    simpa only [mul_inv_cancel₀ hne] using hmul
  have hsum : LSeries (fun n : ℕ => χ n * (μ n : ℂ)) 2 =
      ∑' n : ℕ, if n.Coprime S then (μ n : ℂ) / (n : ℂ) ^ 2 else 0 := by
    rw [LSeries_def₀ (by simp) 2]
    simp only [Complex.cpow_two]
    apply tsum_congr
    intro n
    simp only [χ, fixedU_principal_character_apply]
    split_ifs <;> simp
  rw [← hsum, hinv]
  change (LSeries (fun n : ℕ => (1 : DirichletCharacter ℂ S) n) 2)⁻¹ = _
  rw [fixedU_principal_LSeries_two, mul_inv_rev, Finset.prod_inv_distrib, mul_comm]

/-- The real Euler constant, written using the classical value `ζ(2)=π²/6`. -/
theorem fixedURootEuler_sum (S : ℕ) [NeZero S] :
    (∑' n : ℕ, fixedURootEulerTerm S n) =
      (Real.pi ^ 2 / 6)⁻¹ * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  have hcast (n : ℕ) : (fixedURootEulerTerm S n : ℂ) =
      if n.Coprime S then (μ n : ℂ) / (n : ℂ) ^ 2 else 0 := by
    unfold fixedURootEulerTerm
    split_ifs <;> push_cast <;> rfl
  simp_rw [hcast]
  rw [fixedU_complex_moebius_sum_two, riemannZeta_two]
  push_cast
  rfl

/-- Equivalent real formulation using the real part of the Riemann zeta value. -/
theorem fixedURootEuler_sum_zeta (S : ℕ) [NeZero S] :
    (∑' n : ℕ, fixedURootEulerTerm S n) =
      ((riemannZeta 2).re)⁻¹ * ∏ p ∈ S.primeFactors, (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
  have hz : (riemannZeta 2).re = Real.pi ^ 2 / 6 := by
    rw [riemannZeta_two, ← Complex.ofReal_pow]
    norm_num [pow_two, Complex.mul_re]
  rw [fixedURootEuler_sum, hz]

/-- The exact Euler constant is strictly positive for every positive modulus. -/
theorem fixedURootEuler_sum_pos (S : ℕ) [NeZero S] :
    0 < ∑' n : ℕ, fixedURootEulerTerm S n := by
  rw [fixedURootEuler_sum]
  apply mul_pos
  · exact inv_pos.mpr (div_pos (sq_pos_of_pos Real.pi_pos) (by norm_num))
  · apply Finset.prod_pos
    intro p hp
    apply inv_pos.mpr
    apply sub_pos.mpr
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hpsq : (1 : ℝ) < (p : ℝ) ^ 2 := by nlinarith
    exact (div_lt_one (by positivity : (0 : ℝ) < (p : ℝ) ^ 2)).mpr hpsq

end ArtinMatthews
