module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta


set_option backward.privateInPublic true
@[expose] public section

/-! Exact half-integer Gamma values used in the Bessel Poisson series. -/
namespace ArtinMatthews

open Complex

theorem spectral_gamma_nat_add_half (n : ℕ) :
    Complex.Gamma ((n : ℂ)+1/2) =
      (Real.sqrt Real.pi : ℂ)*((2*n).factorial : ℂ) /
        ((4 : ℂ)^n*(n.factorial : ℂ)) := by
  induction n with
  | zero =>
    simpa only [Nat.cast_zero, zero_add, Nat.mul_zero, Nat.factorial_zero,
      Nat.cast_one, pow_zero, one_mul, mul_one, div_one] using (Complex.Gamma_one_half_eq.trans (by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
      norm_num))
  | succ n ih =>
    have harg : ((n+1 : ℕ) : ℂ)+1/2 = ((n : ℂ)+1/2)+1 := by push_cast; ring
    have hnz : (n : ℂ)+1/2 ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      norm_num [Complex.add_re, Complex.div_re]
      positivity
    rw [harg,Complex.Gamma_add_one _ hnz,ih]
    have htwo : 2*(n+1) = (2*n+1)+1 := by omega
    rw [htwo,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,pow_succ]
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have hn : (n : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have hp : (4 : ℂ)^n ≠ 0 := pow_ne_zero n (by norm_num)
    push_cast
    field_simp
    ring

end ArtinMatthews
