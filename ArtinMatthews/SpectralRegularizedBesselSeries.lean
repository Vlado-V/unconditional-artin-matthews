module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring


set_option backward.privateInPublic true
@[expose] public section

/-! Derivative and contiguous identities for the regularized series in Mathlib's Bessel J.
Both identities hold at the Gamma poles by the reciprocal Gamma recurrence. -/
noncomputable section
open scoped BigOperators ENNReal

namespace ArtinMatthews
open Complex FormalMultilinearSeries

local notation "F(" b ")" => Complex.regularizedHGFun 0 {b}
local notation "P(" b ")" => Complex.regularizedHGFunSeries 0 {b}
local notation "c(" b ")" => Complex.regularizedHGFunCoeff 0 {b}

private theorem regularizedBessel_coeff (b : ℂ) (n : ℕ) :
    c(b) n = ((n.factorial : ℂ) * Complex.Gamma (b+n))⁻¹ := by
  simp [Complex.regularizedHGFunCoeff]

private theorem regularizedBessel_coeff_succ (b : ℂ) (n : ℕ) :
    (n+1 : ℂ)*c(b) (n+1) = c(b+1) n := by
  rw [regularizedBessel_coeff, regularizedBessel_coeff, Nat.factorial_succ]
  push_cast
  rw [show b+((n : ℂ)+1) = b+1+n by ring]
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  simp only [mul_inv, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

theorem spectral_regularizedBessel_hasDerivAt (b z : ℂ) :
    HasDerivAt F(b) (F(b+1) z) z := by
  let p := P(b)
  have hp : ‖z‖ₑ < p.radius := by simp [p]
  have hd := (p.hasFDerivAt_sum hp).hasDerivAt
  have hpd : ‖z‖ₑ < p.derivSeries.radius := hp.trans_le p.radius_le_radius_derivSeries
  have he : (p.derivSeries.sum z) 1 = F(b+1) z := by
    let e := ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)
    change e (∑' n, p.derivSeries n (fun _ => z)) =
      ∑' n, (P(b+1)) n (fun _ => z)
    rw [e.map_tsum (p.derivSeries.summable (by simpa [Metric.mem_eball, edist_zero_right] using hpd))]
    simp only [e, ContinuousLinearMap.apply_apply]
    apply tsum_congr
    intro n
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, ContinuousLinearMap.smul_apply,
      p.derivSeries_coeff_one, show p.coeff n.succ = c(b) (n+1) by
        simp [p, Nat.succ_eq_add_one],
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, Complex.regularizedHGFunSeries_coeff,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one, regularizedBessel_coeff_succ]
  rw [he] at hd
  exact hd

private theorem regularizedBessel_coeff_shift (b : ℂ) (n : ℕ) :
    c(b) n = (b+n)*c(b+1) n := by
  rw [regularizedBessel_coeff, regularizedBessel_coeff, mul_inv, mul_inv,
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b+n)]
  rw [show b+n+1 = b+1+n by ring]
  ring

theorem spectral_regularizedBessel_contiguous (b z : ℂ) :
    F(b) z = b*F(b+1) z + z*F(b+2) z := by
  let f (a : ℂ) (n : ℕ) := z^n*c(a) n
  have hs (a : ℂ) : Summable (f a) := by
    simpa only [f, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      Complex.regularizedHGFunSeries_coeff, smul_eq_mul] using
      (P(a)).summable (x := z) (by simp)
  have hf (a : ℂ) : F(a) z = ∑' n, f a n := by
    simp only [Complex.regularizedHGFun, FormalMultilinearSeries.sum,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, Complex.regularizedHGFunSeries_coeff,
      smul_eq_mul, f]
  let g (n : ℕ) := (n : ℂ)*f (b+1) n
  have hg (n : ℕ) : g (n+1) = z*f (b+2) n := by
    simp only [g, f, Nat.cast_add, Nat.cast_one, pow_succ]
    rw [show (n+1 : ℂ)*(z^n*z*c(b+1) (n+1)) =
      z*z^n*((n+1 : ℂ)*c(b+1) (n+1)) by ring, regularizedBessel_coeff_succ,
      show b+1+1 = b+2 by ring]
    ring
  have hgs : Summable g := (summable_nat_add_iff 1).mp (by
    simpa only [hg] using (hs (b+2)).mul_left z)
  have hgt : (∑' n, g n) = z*F(b+2) z := by
    rw [hgs.tsum_eq_zero_add, hf, ← tsum_mul_left]
    simp only [g, Nat.cast_zero, zero_mul, zero_add]
    exact tsum_congr hg
  rw [hf b, hf (b+1), ← hgt, ← tsum_mul_left, ← ((hs (b+1)).mul_left b).tsum_add hgs]
  apply tsum_congr
  intro n
  dsimp only [f, g]
  rw [regularizedBessel_coeff_shift b n]
  ring

end ArtinMatthews
