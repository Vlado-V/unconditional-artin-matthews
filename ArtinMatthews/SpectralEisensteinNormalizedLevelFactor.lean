module

public import ArtinMatthews.SpectralEisensteinLevelEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The conventional finite Euler factors, including the exact power of the fixed level. -/
noncomputable section
namespace ArtinMatthews

theorem spectralTotient_complex_product (N : ℕ) :
    (N.totient:ℂ)=(N:ℂ)*∏ p ∈ N.primeFactors, (1-(p:ℂ)⁻¹) := by
  have h := congrArg (fun q : ℚ => (q:ℂ)) (Nat.totient_eq_mul_prod_factors N)
  push_cast at h
  exact h

theorem gamma0Eisenstein_level_factor_normalized (N : ℕ) (hN : 0<N) (s : ℂ) :
    (N.totient:ℂ)*(N:ℂ)^(-2*s)/gamma0EisensteinLevelEulerDenominator N s =
      (N:ℂ)^(1-2*s)*∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  have hpow : (N:ℂ)^(1-2*s)=(N:ℂ)*(N:ℂ)^(-2*s) := by
    rw [show (1-2*s:ℂ)=1+(-2*s) by ring,
      Complex.cpow_add _ _ (by exact_mod_cast hN.ne'),Complex.cpow_one]
  rw [spectralTotient_complex_product,hpow,Finset.prod_div_distrib]
  unfold gamma0EisensteinLevelEulerDenominator
  ring

theorem gamma0EisensteinTotientSeries_euler_factors (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinTotientSeries N s = (riemannZeta (2*s-1)/riemannZeta (2*s))*
      (N:ℂ)^(1-2*s)*∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0EisensteinTotientSeries_level N hN s hs,
    gamma0Eisenstein_level_factor_normalized N hN s]
  ring

end ArtinMatthews
