module

public import ArtinMatthews.SpectralEisensteinPrimeStep
public import ArtinMatthews.SpectralEisensteinEulerDenominator
public import ArtinMatthews.SpectralEisensteinTotientLSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite-level Euler factors, proved by adjoining primes to the level. -/
noncomputable section
namespace ArtinMatthews

theorem gamma0EisensteinTotientSeries_level_cross (N : ℕ) (hN : 0<N)
    (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinLevelEulerDenominator N s*gamma0EisensteinTotientSeries N s =
      (N.totient:ℂ)*(N:ℂ)^(-2*s)*gamma0EisensteinTotientSeries 1 s := by
  have hmain : ∀ M : ℕ, 0<M →
      gamma0EisensteinLevelEulerDenominator M s*gamma0EisensteinTotientSeries M s =
        (M.totient:ℂ)*(M:ℂ)^(-2*s)*gamma0EisensteinTotientSeries 1 s := by
    apply induction_on_primes
    · intro h
      omega
    · intro _
      simp [gamma0EisensteinLevelEulerDenominator_one]
    · intro p M hp hM hpos
      have hMpos : 0<M := Nat.pos_of_mul_pos_left hpos
      have hih := hM hMpos
      by_cases hpM : p∣M
      · rw [gamma0EisensteinLevelEulerDenominator_existing M p hMpos hp hpM s,
          gamma0EisensteinTotientSeries_prime_existing M p hp hpM s hs,
          Nat.totient_mul_of_prime_of_dvd hp hpM,Nat.cast_mul,Nat.cast_mul,
          Complex.natCast_mul_natCast_cpow]
        linear_combination (p:ℂ)*(p:ℂ)^(-2*s)*hih
      · rw [gamma0EisensteinLevelEulerDenominator_new M p hMpos hp hpM s,
          Nat.totient_mul_of_prime_of_not_dvd hp hpM,Nat.cast_mul,Nat.cast_sub hp.one_le,
          Nat.cast_one,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
        have hstep := gamma0EisensteinTotientSeries_prime_new M p hp hpM s hs
        linear_combination gamma0EisensteinLevelEulerDenominator M s*hstep +
          ((p:ℂ)-1)*(p:ℂ)^(-2*s)*hih
  exact hmain N hN

theorem gamma0EisensteinTotientSeries_level (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries N s =
      ((N.totient:ℂ)*(N:ℂ)^(-2*s)/gamma0EisensteinLevelEulerDenominator N s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s)) := by
  have h := gamma0EisensteinTotientSeries_level_cross N hN s hs
  rw [gamma0EisensteinTotientSeries_one s hs] at h
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (gamma0EisensteinLevelEulerDenominator_ne_zero N s hs)).mpr
  linear_combination h

theorem gamma0EisensteinTotientSeries_level_explicit (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries N s =
      (riemannZeta (2*s-1)/riemannZeta (2*s))*
        ((N.totient:ℂ)*(N:ℂ)^(-2*s)/∏ p ∈ N.primeFactors, (1-(p:ℂ)^(-2*s))) := by
  rw [gamma0EisensteinTotientSeries_level N hN s hs]
  exact mul_comm _ _

end ArtinMatthews
