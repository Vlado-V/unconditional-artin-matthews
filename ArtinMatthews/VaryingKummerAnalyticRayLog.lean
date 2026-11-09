module

public import ArtinMatthews.VaryingKummerAnalyticRayEuler
public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine holomorphic Euler logarithm of the arbitrary-field ray series.
The modulus omissions remain in the actual zero-extended coefficients. -/

namespace ArtinMatthews.VaryingKummerAnalytic
noncomputable section
open NumberField Set Filter
open OAI.PrimeDegreePackets
open scoped NumberField Classical BigOperators Topology
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

def eulerRatio (I : Ideal (𝓞 K)) (s : ℂ) : ℂ :=
  ψ.allCoefficient I * (Ideal.absNorm I : ℂ) ^ (-s)

theorem idealTerm_eq_eulerRatio {s : ℂ} (hs : 1 < s.re) (I : Ideal (𝓞 K)) :
    ψ.idealTerm hs I = ψ.eulerRatio I s := rfl

theorem eulerRatio_norm_le {I : Ideal (𝓞 K)} (hI : 2 ≤ Ideal.absNorm I)
    {s : ℂ} {σ : ℝ} (hs : σ ≤ s.re) :
    ‖ψ.eulerRatio I s‖ ≤ (Ideal.absNorm I : ℝ) ^ (-σ) := by
  have hNpos : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast (by omega : 0 < Ideal.absNorm I)
  calc
    _ ≤ ‖(Ideal.absNorm I : ℂ) ^ (-s)‖ := by
      rw [eulerRatio, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (ψ.allCoefficient_norm_le_one I)
    _ ≤ _ := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos, Complex.neg_re]
      exact Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (by omega : 1 ≤ Ideal.absNorm I)) (neg_le_neg hs)

theorem eulerRatio_norm_le_half {I : Ideal (𝓞 K)} (hI : 2 ≤ Ideal.absNorm I)
    {s : ℂ} (hs : 1 ≤ s.re) : ‖ψ.eulerRatio I s‖ ≤ 1 / 2 := by
  apply (ψ.eulerRatio_norm_le hI hs).trans
  rw [Real.rpow_neg_one]
  have hN : (2 : ℝ) ≤ Ideal.absNorm I := by exact_mod_cast hI
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN

def eulerLocalLog (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑ P : idealsOverPrime K p, -Complex.log (1 - ψ.eulerRatio P.val s)

def eulerLog (s : ℂ) : ℂ := ∑' p : Nat.Primes, ψ.eulerLocalLog p s

theorem eulerLocalLog_norm_le (p : Nat.Primes)
    {s : ℂ} {σ : ℝ} (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖ψ.eulerLocalLog p s‖ ≤ dedekindEulerLogMajorant K σ p := by
  have hlog (P : idealsOverPrime K p) :
      ‖-Complex.log (1 - ψ.eulerRatio P.val s)‖ ≤ 2 * (Ideal.absNorm P.val : ℝ) ^ (-σ) := by
    have hhalf := ψ.eulerRatio_norm_le_half (idealsOverPrime_norm_two_le K P.property) (hσ.trans hs)
    have hl := Complex.norm_log_one_add_half_le_self
      (z := -ψ.eulerRatio P.val s) (by simpa using hhalf)
    simp only [norm_neg, ← sub_eq_add_neg] at hl
    rw [norm_neg]
    calc
      _ ≤ (3 / 2) * ‖ψ.eulerRatio P.val s‖ := hl
      _ ≤ (3 / 2) * (Ideal.absNorm P.val : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_left
          (ψ.eulerRatio_norm_le (idealsOverPrime_norm_two_le K P.property) hs) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  calc
    _ ≤ ∑ P : idealsOverPrime K p, ‖-Complex.log (1 - ψ.eulerRatio P.val s)‖ := norm_sum_le _ _
    _ ≤ ∑ P : idealsOverPrime K p, 2 * (Ideal.absNorm P.val : ℝ) ^ (-σ) :=
      Finset.sum_le_sum (fun P _ => hlog P)
    _ = 2 * ∑ P : idealsOverPrime K p, (Ideal.absNorm P.val : ℝ) ^ (-σ) := (Finset.mul_sum ..).symm
    _ ≤ 2 * ((Module.finrank ℚ K : ℝ) * (p : ℝ) ^ (-σ)) :=
      mul_le_mul_of_nonneg_left (prime_ideal_norm_series_le K p (by linarith)) (by norm_num)
    _ = _ := by unfold dedekindEulerLogMajorant; ring

theorem eulerLocalLog_differentiableOn (p : Nat.Primes) :
    DifferentiableOn ℂ (ψ.eulerLocalLog p) {s : ℂ | 1 < s.re} := by
  apply DifferentiableOn.fun_sum
  intro P _ s hs
  have hn : ‖ψ.eulerRatio P.val s‖ < 1 := by
    simpa only [idealTerm_eq_eulerRatio] using ψ.prime_idealTerm_norm_lt_one hs P
  have hslit : 1 - ψ.eulerRatio P.val s ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one
      (z := -ψ.eulerRatio P.val s) (by simpa using hn)
  have hN : (Ideal.absNorm P.val : ℂ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm P.val ≠ 0 by
      have h := idealsOverPrime_norm_two_le K P.property
      omega)
  have hd : Differentiable ℂ (ψ.eulerRatio P.val) :=
    (differentiable_id.neg.const_cpow (Or.inl hN)).const_mul (ψ.allCoefficient P.val)
  exact ((Complex.differentiableAt_log hslit).comp s
    ((differentiableAt_const (1 : ℂ)).sub (hd s))).neg.differentiableWithinAt

theorem eulerLog_differentiableOn_halfplane {σ : ℝ} (hσ : 1 < σ) :
    DifferentiableOn ℂ ψ.eulerLog {s : ℂ | σ < s.re} := by
  apply Complex.differentiableOn_tsum_of_summable_norm (dedekindEulerLogMajorant_summable K hσ)
  · intro p
    exact (ψ.eulerLocalLog_differentiableOn p).mono (fun s hs => hσ.trans hs)
  · exact isOpen_lt continuous_const Complex.continuous_re
  · intro p s hs
    exact ψ.eulerLocalLog_norm_le p hσ.le hs.le

theorem eulerLog_differentiableOn : DifferentiableOn ℂ ψ.eulerLog {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  have hσ : 1 < (1 + s.re) / 2 := by linarith
  have hmem : s ∈ {z : ℂ | (1 + s.re) / 2 < z.re} := by dsimp; linarith
  exact ((ψ.eulerLog_differentiableOn_halfplane hσ s hmem).differentiableAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hmem)).differentiableWithinAt

theorem eulerLog_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes => ψ.eulerLocalLog p s) := by
  have h := (dedekindEulerLogMajorant_summable K hs).of_nonneg_of_le
    (fun p => norm_nonneg (ψ.eulerLocalLog p s))
    (fun p => ψ.eulerLocalLog_norm_le p hs.le le_rfl)
  exact h.of_norm

theorem eulerLocalLog_exp (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (ψ.eulerLocalLog p s) =
      ∏ P : idealsOverPrime K p, (1 - ψ.idealTerm hs P.val)⁻¹ := by
  unfold eulerLocalLog
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro P _
  have hn : ‖ψ.eulerRatio P.val s‖ < 1 := by
    simpa only [idealTerm_eq_eulerRatio] using ψ.prime_idealTerm_norm_lt_one hs P
  have hne : 1 - ψ.eulerRatio P.val s ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    rw [he, norm_one] at hn
    exact (lt_irrefl _ hn)
  rw [Complex.exp_neg, Complex.exp_log hne, idealTerm_eq_eulerRatio]

theorem dirichlet_hasProd_exp_localLog {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => Complex.exp (ψ.eulerLocalLog p s)) (ψ.dirichlet s) := by
  have he (p : Nat.Primes) := ψ.eulerLocalLog_exp p hs
  simpa only [he] using ψ.dirichlet_hasProd hs

/-- This is an actual analytic logarithm of the literal ray Dirichlet series. -/
theorem exp_eulerLog_eq_dirichlet {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (ψ.eulerLog s) = ψ.dirichlet s := by
  have h := (ψ.eulerLog_summable hs).hasSum.cexp
  exact h.unique (ψ.dirichlet_hasProd_exp_localLog hs)

/-- A universal degree bound, independent of the actual character and modulus. -/
theorem eulerLog_norm_le {s : ℂ} (hs : 5 / 4 ≤ s.re) :
    ‖ψ.eulerLog s‖ ≤ (Module.finrank ℚ K : ℝ) * dedekindEulerLogConstant := by
  have hsum := dedekindEulerLogMajorant_summable K (by norm_num : (1 : ℝ) < 5 / 4)
  have hpoint (p : Nat.Primes) : ‖ψ.eulerLocalLog p s‖ ≤ dedekindEulerLogMajorant K (5 / 4) p :=
    ψ.eulerLocalLog_norm_le p (by norm_num) hs
  have hnorm := hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
  calc
    _ ≤ ∑' p : Nat.Primes, ‖ψ.eulerLocalLog p s‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' p : Nat.Primes, dedekindEulerLogMajorant K (5 / 4) p :=
      hnorm.tsum_le_tsum hpoint hsum
    _ = (Module.finrank ℚ K : ℝ) * (2 * ∑' p : Nat.Primes, (p : ℝ) ^ (-(5 / 4 : ℝ))) := by
      simp only [dedekindEulerLogMajorant, tsum_mul_left]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      unfold dedekindEulerLogConstant
      linarith

end EvenRayCharacter
end
end ArtinMatthews.VaryingKummerAnalytic
