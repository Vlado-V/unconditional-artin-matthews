module

public import ArtinMatthews.MarkedMajorArcHighPrimeNormalized
public import ArtinMatthews.MarkedMajorArcProductBudget
public import ArtinMatthews.MarkedMajorArcProductMean
public import Mathlib.NumberTheory.Harmonic.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Ordinary mean squares with the original normalized polynomial factors. -/

namespace ArtinMatthews

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

theorem sourceComparisonPrimePhase_eq_cpow {n : ℕ} (hn : 0 < n) (t : ℝ) :
    markedPrimePhase n t = (n:ℂ)^((t:ℂ)*Complex.I) := by
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log, markedPrimePhase]
  congr 1
  push_cast
  ring

theorem sourceComparisonDyadicPolynomial_eq_natural (l r : ℕ) (U : ℝ)
    (a : ℕ → ℂ) (t : ℝ) :
    markedDyadicPolynomial l r U a t =
      markedNaturalPolynomial (Icc l r) (fun n => a n / U) t := by
  unfold markedDyadicPolynomial markedNaturalPolynomial
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  ring

theorem sourceComparisonDyadicPolynomial_mean_square (l r : ℕ) (U T : ℝ)
    (a : ℕ → ℂ) (hU : 0 < U) (hT : 0 < T)
    (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U) :
    (∫ t in Set.Icc (-T) T, ‖markedDyadicPolynomial l r U a t‖^2) ≤
      8*Real.exp 1*(T+2*U)*(∑ n ∈ Icc l r, ‖a n/U‖^2) := by
  have hl0 : 0 < l := by exact_mod_cast hU.trans_le hl
  have hS : Icc l r ⊆ Ioc 0 r := by
    intro n hn
    exact mem_Ioc.mpr ⟨hl0.trans_le (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩
  have h := markedNaturalPolynomial_mean_square (Icc l r) hS (fun n => a n/(U:ℂ)) hT
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at h
  simp_rw [sourceComparisonDyadicPolynomial_eq_natural]
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (add_le_add_right hr _) (by positivity)) (by positivity))

theorem sourceComparisonDyadicCoefficient_square_mass (l r : ℕ) (U M : ℝ) (a : ℕ → ℂ)
    (hU : 0 < U) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (ha : ∀ n ∈ Icc l r, ‖a n‖ ≤ M) :
    (∑ n ∈ Icc l r, ‖a n/U‖^2) ≤ 2*M^2/U := by
  have hl0 : 0 < l := by exact_mod_cast hU.trans_le hl
  have hS : Icc l r ⊆ Ioc 0 r := by
    intro n hn
    exact mem_Ioc.mpr ⟨hl0.trans_le (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩
  have hc : ((Icc l r).card:ℝ) ≤ (r:ℝ) := by
    exact_mod_cast (card_le_card hS).trans_eq (by simp)
  calc
    _ ≤ ∑ _n ∈ Icc l r, (M/U)^2 := by
      apply sum_le_sum
      intro n hn
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
      exact pow_le_pow_left₀ (by positivity)
        (div_le_div_of_nonneg_right (ha n hn) hU.le) 2
    _ = ((Icc l r).card:ℝ)*(M/U)^2 := by simp
    _ ≤ (2*U)*(M/U)^2 := mul_le_mul_of_nonneg_right (hc.trans hr) (sq_nonneg _)
    _ = _ := by field_simp <;> ring

theorem sourceComparisonNormalizedPrime_eq_natural {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t H u v : ℝ) :
    markedMajorNormalizedPrimeSum χ t H u v =
      markedNaturalPolynomial ((Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime)
        (fun n => χ (n:ZMod q)/H) t := by
  unfold markedMajorNormalizedPrimeSum markedNaturalPolynomial
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [sourceComparisonPrimePhase_eq_cpow (mem_filter.mp hn).2.pos]
  ring

theorem sourceComparisonNormalizedPrime_continuous {q : ℕ} (χ : DirichletCharacter ℂ q)
    (H u v : ℝ) : Continuous (fun t => markedMajorNormalizedPrimeSum χ t H u v) := by
  simp_rw [sourceComparisonNormalizedPrime_eq_natural]
  exact markedNaturalPolynomial_continuous _ _

/-- The product mean for the positive giant-prime branch. The prime factor
is the actual normalized prime sum on the prescribed dyad. -/
theorem sourceComparisonPrimeProduct_mean_square {q : ℕ} (χ : DirichletCharacter ℂ q)
    (H u v U T M : ℝ) (l r : ℕ) (a : ℕ → ℂ)
    (hH : 0 < H) (hU : 0 < U) (hHU : 1 ≤ H*U) (hT : 0 < T)
    (hHu : H ≤ u) (hv : v ≤ 2*H) (hl : U ≤ (l:ℝ)) (hr : (r:ℝ) ≤ 2*U)
    (hM : 0 ≤ M) (ha : ∀ n ∈ Icc l r, ‖a n‖ ≤ M) :
    (∫ t in Set.Icc (-T) T,
      ‖markedMajorNormalizedPrimeSum χ t H u v * markedDyadicPolynomial l r U a t‖^2) ≤
      128*Real.exp 1*(1+T/(H*U))*M^2*(1+Real.log (4*H*U))^3 := by
  let S := (Ioc ⌊u⌋₊ ⌊v⌋₊).filter Nat.Prime
  let N := ⌊4*H*U⌋₊
  let c : ℕ → ℂ := fun n => χ (n:ZMod q)/H
  let b : ℕ → ℂ := fun n => a n/U
  have hS : ∀ m ∈ S, 0 < m := fun m hm => (mem_filter.mp hm).2.pos
  have hR : ∀ n ∈ Icc l r, 0 < n := by
    intro n hn
    have hnL : (l:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    exact_mod_cast hU.trans_le (hl.trans hnL)
  have hsupport : ∀ m ∈ S, ∀ n ∈ Icc l r, m*n ≤ N := by
    intro m hm n hn
    have hmf : (m:ℝ) ≤ (⌊v⌋₊:ℝ) := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hm).1).2
    have hv0 : 0 ≤ v := by
      have hfloor : 0 < ⌊v⌋₊ := (hS m hm).trans_le (mem_Ioc.mp (mem_filter.mp hm).1).2
      exact zero_le_one.trans (Nat.floor_pos.mp hfloor)
    have hmv : (m:ℝ) ≤ 2*H := hmf.trans ((Nat.floor_le hv0).trans hv)
    have hnu : (n:ℝ) ≤ 2*U := (show (n:ℝ) ≤ r by exact_mod_cast (mem_Icc.mp hn).2).trans hr
    apply (Nat.le_floor_iff (by positivity : (0:ℝ) ≤ 4*H*U)).mpr
    rw [Nat.cast_mul]
    nlinarith [mul_le_mul hmv hnu (Nat.cast_nonneg n) (by positivity : (0:ℝ) ≤ 2*H)]
  have hc : ∀ n ∈ S, ‖c n‖ ≤ 1/H := by
    intro n _
    dsimp [c]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH]
    exact div_le_div_of_nonneg_right (χ.norm_le_one _) hH.le
  have hb : ∀ n ∈ Icc l r, ‖b n‖ ≤ M/U := by
    intro n hn
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hU]
    exact div_le_div_of_nonneg_right (ha n hn) hU.le
  have hmean := markedNaturalPolynomial_product_mean_square S (Icc l r) c b
    N (1/H) (M/U) 0 T (by positivity) (by positivity) hT hS hR hsupport hc hb
  simp only [add_zero] at hmean
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc] at hmean
  simp_rw [sourceComparisonNormalizedPrime_eq_natural, sourceComparisonDyadicPolynomial_eq_natural]
  have hharm : (∑ d ∈ Icc 1 N,1/(d:ℝ)) ≤ 1+Real.log (N:ℝ) := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
      using harmonic_le_one_add_log N
  calc
    _ ≤ markedProductMeanEnvelope H U T 1 M := by
      apply hmean.trans
      unfold markedProductMeanEnvelope
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hharm 3
    _ ≤ _ := by simpa only [one_pow, mul_one] using
      marked_product_mean_envelope_bound H U T 1 M hH hU hHU hT.le

end
end ArtinMatthews
