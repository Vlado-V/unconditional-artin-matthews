module

public import ArtinMatthews.VaryingKummerAnalyticDedekindEulerPrimeNorm
public import ArtinMatthews.VaryingKummerAnalyticDedekindNonvanishing


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine holomorphic Euler logarithm of Dedekind zeta, with a
fixed-half-plane bound linear in the actual field degree. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set Filter
open OAI.PrimeDegreePackets
open scoped NumberField Classical BigOperators Topology

private theorem norm_nat_cpow_neg_le {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖(N : ℂ) ^ (-s)‖ ≤ (N : ℝ) ^ (-σ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N))
    (neg_le_neg hs)

private theorem norm_nat_cpow_neg_le_half {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} (hs : 1 ≤ s.re) : ‖(N : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  apply (norm_nat_cpow_neg_le hN hs).trans
  rw [Real.rpow_neg_one]
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  simpa only [one_div] using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hNreal

private theorem log_normPower_factor_norm_le {N : ℕ} (hN : 2 ≤ N)
    {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖-Complex.log (1 - (N : ℂ) ^ (-s))‖ ≤ 2 * (N : ℝ) ^ (-σ) := by
  have hhalf := norm_nat_cpow_neg_le_half hN (hσ.trans hs)
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := -(N : ℂ) ^ (-s)) (by simpa using hhalf)
  simp only [norm_neg, ← sub_eq_add_neg] at hlog
  rw [norm_neg]
  calc
    _ ≤ (3 / 2) * ‖(N : ℂ) ^ (-s)‖ := hlog
    _ ≤ (3 / 2) * (N : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_left (norm_nat_cpow_neg_le hN hs) (by norm_num)
    _ ≤ 2 * (N : ℝ) ^ (-σ) :=
      mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _)

variable (K : Type*) [Field K] [NumberField K]

def dedekindEulerLocalLog (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑ P : idealsOverPrime K p, -Complex.log (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))

def dedekindEulerLog (s : ℂ) : ℂ := ∑' p : Nat.Primes, dedekindEulerLocalLog K p s

def dedekindEulerLogMajorant (σ : ℝ) (p : Nat.Primes) : ℝ :=
  (2 * (Module.finrank ℚ K : ℝ)) * (p : ℝ) ^ (-σ)

theorem dedekindEulerLocalLog_norm_le (p : Nat.Primes)
    {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖dedekindEulerLocalLog K p s‖ ≤ dedekindEulerLogMajorant K σ p := by
  calc
    _ ≤ ∑ P : idealsOverPrime K p,
        ‖-Complex.log (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))‖ := norm_sum_le _ _
    _ ≤ ∑ P : idealsOverPrime K p, 2 * (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
      apply Finset.sum_le_sum
      intro P _
      exact log_normPower_factor_norm_le (idealsOverPrime_norm_two_le K P.property) hσ hs
    _ = 2 * ∑ P : idealsOverPrime K p, (Ideal.absNorm P.val : ℝ) ^ (-σ) :=
      (Finset.mul_sum ..).symm
    _ ≤ 2 * ((Module.finrank ℚ K : ℝ) * (p : ℝ) ^ (-σ)) :=
      mul_le_mul_of_nonneg_left (prime_ideal_norm_series_le K p (by linarith)) (by norm_num)
    _ = _ := by unfold dedekindEulerLogMajorant; ring

theorem dedekindEulerLogMajorant_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (dedekindEulerLogMajorant K σ) :=
  (prime_rpow_summable hσ).mul_left (2 * (Module.finrank ℚ K : ℝ))

private theorem normPower_factor_differentiableOn (p : Nat.Primes)
    (P : idealsOverPrime K p) :
    DifferentiableOn ℂ (fun s : ℂ => -Complex.log (1 - (Ideal.absNorm P.val : ℂ) ^ (-s)))
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hn : ‖(Ideal.absNorm P.val : ℂ) ^ (-s)‖ < 1 :=
    zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  have hslit : 1 - (Ideal.absNorm P.val : ℂ) ^ (-s) ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -(Ideal.absNorm P.val : ℂ) ^ (-s)) (by simpa using hn)
  have hN : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm P.val ≠ 0 by
      have h := idealsOverPrime_norm_two_le K P.property
      omega)
  have hd : Differentiable ℂ (fun z : ℂ => (Ideal.absNorm P.val : ℂ) ^ (-z)) :=
    differentiable_id.neg.const_cpow (Or.inl hN)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (hd s))).neg.differentiableWithinAt

theorem dedekindEulerLocalLog_differentiableOn (p : Nat.Primes) :
    DifferentiableOn ℂ (dedekindEulerLocalLog K p) {s : ℂ | 1 < s.re} := by
  exact DifferentiableOn.fun_sum (fun P _ => normPower_factor_differentiableOn K p P)

theorem dedekindEulerLog_differentiableOn_halfplane {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ (dedekindEulerLog K) {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (dedekindEulerLogMajorant_summable K hσ)
  · intro p
    exact (dedekindEulerLocalLog_differentiableOn K p).mono (fun s hs => hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact dedekindEulerLocalLog_norm_le K p hσ.le hs.le

theorem dedekindEulerLog_differentiableOn :
    DifferentiableOn ℂ (dedekindEulerLog K) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {z : ℂ | (1 + s.re) / 2 < z.re} := by dsimp; linarith
  exact ((dedekindEulerLog_differentiableOn_halfplane K hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem dedekindEulerLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => dedekindEulerLocalLog K p s) := by
  have h := (dedekindEulerLogMajorant_summable K hs).of_nonneg_of_le
    (fun p => norm_nonneg (dedekindEulerLocalLog K p s))
    (fun p => dedekindEulerLocalLog_norm_le K p hs.le le_rfl)
  exact h.of_norm

theorem dedekindEulerLocalLog_exp (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (dedekindEulerLocalLog K p s) =
      ∏ P : idealsOverPrime K p, (1 - (Ideal.absNorm P.val : ℂ) ^ (-s))⁻¹ := by
  unfold dedekindEulerLocalLog
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro P _
  have hn : ‖(Ideal.absNorm P.val : ℂ) ^ (-s)‖ < 1 :=
    zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.property)
  have hne : 1 - (Ideal.absNorm P.val : ℂ) ^ (-s) ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hn
    exact (lt_irrefl _ hn)
  rw [Complex.exp_neg, Complex.exp_log hne]

theorem dedekindZeta_hasProd_exp_localLog {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => Complex.exp (dedekindEulerLocalLog K p s))
      (NumberField.dedekindZeta K s) := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f, H, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm, idealCoefficientReal, ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f, idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m * f n := by
    simp only [f, (idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul, map_mul]
    ring
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  have hlocal (p : Nat.Primes) : (∑' k : ℕ, f ((p : ℕ) ^ k)) =
      Complex.exp (dedekindEulerLocalLog K p s) := by
    change (∑' k : ℕ, (idealCoefficient K ((p : ℕ) ^ k) : ℂ) * H ((p : ℕ) ^ k)) = _
    rw [ideal_local_complex_euler K hs p.property]
    exact (dedekindEulerLocalLog_exp K p hs).symm
  simpa only [hlocal, he] using EulerProduct.eulerProduct_hasProd h1 (fun h => hm h) hS h0

/-- This is an actual analytic logarithm of the actual Mathlib Dedekind zeta
function on its half-plane of convergence. -/
theorem exp_dedekindEulerLog_eq_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (dedekindEulerLog K s) = NumberField.dedekindZeta K s := by
  have h := (dedekindEulerLog_summable K hs).hasSum.cexp
  exact h.unique (dedekindZeta_hasProd_exp_localLog K hs)

end

/-- A universal finite constant, independent of the number field. -/
noncomputable def dedekindEulerLogConstant : ℝ :=
  1 + 2 * ∑' p : Nat.Primes, (p : ℝ) ^ (-(5 / 4 : ℝ))

theorem dedekindEulerLogConstant_pos : 0 < dedekindEulerLogConstant := by
  have h : 0 ≤ ∑' p : Nat.Primes, (p : ℝ) ^ (-(5 / 4 : ℝ)) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  unfold dedekindEulerLogConstant
  linarith

theorem dedekindEulerLog_norm_le (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 5 / 4 ≤ s.re) :
    ‖dedekindEulerLog K s‖ ≤ (Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant := by
  have hsum := dedekindEulerLogMajorant_summable K (by norm_num : (1 : ℝ) < 5 / 4)
  have hpoint (p : Nat.Primes) : ‖dedekindEulerLocalLog K p s‖ ≤
      dedekindEulerLogMajorant K (5 / 4) p :=
    dedekindEulerLocalLog_norm_le K p (by norm_num) hs
  have hnorm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  calc
    _ ≤ ∑' p : Nat.Primes, ‖dedekindEulerLocalLog K p s‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes, dedekindEulerLogMajorant K (5 / 4) p :=
      hnorm.tsum_le_tsum hpoint hsum
    _ = (Module.finrank ℚ K : ℝ) *
        (2 * ∑' p : Nat.Primes, (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
      simp only [dedekindEulerLogMajorant, tsum_mul_left]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      unfold dedekindEulerLogConstant
      linarith

end ArtinMatthews.VaryingKummerAnalytic
