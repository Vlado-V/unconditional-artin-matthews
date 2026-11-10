module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import ArtinMatthews.ShiftedVoronoiBessel
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Normed.Module.Connected


set_option backward.privateInPublic true
@[expose] public section

/-! The shifted factorial series give the spatial derivatives of the actual
order-zero Bessel kernel. The convergence estimates are uniform on each
complex ball. -/

namespace ArtinMatthews
open Set Filter
noncomputable section

private def jFactorialTerm (j n : ℕ) (z : ℂ) : ℂ :=
  z ^ n / (n.factorial : ℂ) / ((n + j).factorial : ℂ)

def spectralJFactorialSeries (j : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, jFactorialTerm j n z

private def shiftedJFactorialTerm (j : ℕ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => jFactorialTerm j n

private theorem jFactorialTerm_norm_le (j n : ℕ) (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) :
    ‖jFactorialTerm j n z‖ ≤ R ^ n / (n.factorial : ℝ) := by
  have hfac : (1 : ℝ) ≤ (n + j).factorial := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (n + j))
  simp only [jFactorialTerm, norm_div, norm_pow, Complex.norm_natCast]
  exact (div_le_self (by positivity) hfac).trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity))

private theorem jFactorialTerm_summable (j : ℕ) (z : ℂ) :
    Summable (fun n => jFactorialTerm j n z) :=
  (Real.summable_pow_div_factorial ‖z‖).of_norm_bounded
    (fun n => jFactorialTerm_norm_le j n z ‖z‖ le_rfl)

private theorem shiftedJFactorialTerm_summable (j : ℕ) (z : ℂ) :
    Summable (fun n => shiftedJFactorialTerm j n z) := by
  apply (summable_nat_add_iff 1).mp
  exact jFactorialTerm_summable j z

private theorem shiftedJFactorialTerm_tsum (j : ℕ) (z : ℂ) :
    (∑' n, shiftedJFactorialTerm j n z) = spectralJFactorialSeries j z := by
  rw [(shiftedJFactorialTerm_summable j z).tsum_eq_zero_add]
  simp only [shiftedJFactorialTerm, zero_add, spectralJFactorialSeries]

private theorem jFactorialTerm_hasDerivAt (j n : ℕ) (z : ℂ) :
    HasDerivAt (jFactorialTerm j n) (shiftedJFactorialTerm (j + 1) n z) z := by
  cases n with
  | zero =>
    have he : jFactorialTerm j 0 = fun _ => 1 / (j.factorial : ℂ) := by
      funext q
      simp [jFactorialTerm]
    rw [he]
    exact hasDerivAt_const z (1 / (j.factorial : ℂ))
  | succ n =>
    have h : HasDerivAt (jFactorialTerm j (n + 1))
        (((n + 1 : ℕ) : ℂ) * z ^ n / ((n + 1).factorial : ℂ) /
          ((n + 1 + j).factorial : ℂ)) z := by
      unfold jFactorialTerm
      simpa only [Nat.add_sub_cancel, mul_one] using
        (((hasDerivAt_id' z).fun_pow (n + 1)).div_const ((n + 1).factorial : ℂ)).div_const
          ((n + 1 + j).factorial : ℂ)
    convert h using 1
    simp only [shiftedJFactorialTerm, jFactorialTerm, show n + (j + 1) = n + 1 + j by omega,
      Nat.factorial_succ, Nat.cast_mul]
    have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    congr 1
    field_simp

theorem spectralJFactorialSeries_hasDerivAt (j : ℕ) (z : ℂ) :
    HasDerivAt (spectralJFactorialSeries j) (spectralJFactorialSeries (j + 1) z) z := by
  let R := ‖z‖ + 1
  let u : ℕ → ℝ
    | 0 => 0
    | n + 1 => R ^ n / (n.factorial : ℝ)
  have hu : Summable u := by
    apply (summable_nat_add_iff 1).mp
    exact Real.summable_pow_div_factorial R
  have h0 : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self (by dsimp [R]; positivity)
  have hz : z ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_add_one _
  have hb (n : ℕ) (q : ℂ) (hq : q ∈ Metric.ball 0 R) :
      ‖shiftedJFactorialTerm (j + 1) n q‖ ≤ u n := by
    cases n with
    | zero => simp [shiftedJFactorialTerm, u]
    | succ n =>
      exact jFactorialTerm_norm_le _ _ _ _ (by
        rw [Metric.mem_ball, dist_zero_right] at hq
        exact hq.le)
  have h := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball Metric.isPreconnected_ball
    (fun n q _ => jFactorialTerm_hasDerivAt j n q) hb h0 (jFactorialTerm_summable j 0) hz
  rw [shiftedJFactorialTerm_tsum] at h
  exact h

/-- The coefficient recurrence giving (z U_2(z)+U_1(z)=U_0(z)). -/
theorem spectralJFactorialSeries_ode (z : ℂ) :
    spectralJFactorialSeries 1 z + z * spectralJFactorialSeries 2 z =
      spectralJFactorialSeries 0 z := by
  have hterm (n : ℕ) :
      jFactorialTerm 1 n z + z * shiftedJFactorialTerm 2 n z = jFactorialTerm 0 n z := by
    cases n with
    | zero => norm_num [jFactorialTerm, shiftedJFactorialTerm]
    | succ n =>
      simp only [jFactorialTerm, shiftedJFactorialTerm, Nat.add_zero, pow_succ]
      simp only [show n + 1 + 1 = n + 2 by omega, Nat.factorial_succ, Nat.cast_mul]
      have h₀ : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have h₁ : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      have h₂ : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      field_simp
      push_cast
      ring
  rw [← shiftedJFactorialTerm_tsum 2 z, ← tsum_mul_left, spectralJFactorialSeries,
    ← (jFactorialTerm_summable 1 z).tsum_add ((shiftedJFactorialTerm_summable 2 z).mul_left z)]
  exact tsum_congr hterm

theorem spectralJFactorialSeries_zero_eq_besselJ (t : ℝ) (ht : 0 ≤ t) :
    spectralJFactorialSeries 0 (-(t : ℂ)) = Complex.besselJ 0 (2 * (Real.sqrt t : ℂ)) := by
  rw [← (hasSum_besselJ_zero_sqrt t ht).tsum_eq]
  apply tsum_congr
  intro n
  simp only [jFactorialTerm, Nat.add_zero, div_div, pow_two]

end
end ArtinMatthews
