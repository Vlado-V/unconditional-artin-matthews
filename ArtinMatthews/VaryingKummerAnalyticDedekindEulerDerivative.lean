module

public import ArtinMatthews.VaryingKummerAnalyticDedekindLogDerivativeBound


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine differentiation of the locally uniformly convergent actual
Dedekind Euler logarithm. -/

namespace ArtinMatthews.VaryingKummerAnalytic

open Set

theorem dedekindEulerLog_hasSum_deriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => deriv (dedekindEulerLocalLog K p) s)
      (deriv (dedekindEulerLog K) s) := by
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs
  exact Complex.hasSum_deriv_of_summable_norm (dedekindEulerLogMajorant_summable K hσ)
    (fun p => (dedekindEulerLocalLog_differentiableOn K p).mono (fun z hz => hσ.trans hz))
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun p z hz => dedekindEulerLocalLog_norm_le K p hσ.le (le_of_lt hz)) hσs

theorem dedekindZeta_logDeriv_hasSum_deriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun p : Nat.Primes => deriv (dedekindEulerLocalLog K p) s)
      (logDeriv (NumberField.dedekindZeta K) s) := by
  rw [dedekindZeta_logDeriv_eq_deriv_eulerLog K hs]
  exact dedekindEulerLog_hasSum_deriv K hs

end ArtinMatthews.VaryingKummerAnalytic
