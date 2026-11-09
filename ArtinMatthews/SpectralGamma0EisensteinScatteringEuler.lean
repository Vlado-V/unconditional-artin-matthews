module

public import ArtinMatthews.SpectralEisensteinNormalizedLevelFactor


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinity scattering coefficient and actual constant term with finite level factors. -/
noncomputable section
open MeasureTheory
namespace ArtinMatthews

theorem gamma0EisensteinScatteringInfinity_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re) :
    gamma0EisensteinScatteringInfinity N s =
      ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  unfold gamma0EisensteinScatteringInfinity
  rw [gamma0EisensteinTotientSeries_euler_factors N hN s hs]
  ring

theorem gamma0Eisenstein_infinity_constant_term_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) = (y:ℂ)^s+
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0Eisenstein_infinity_constant_term N s hs y hy,
    gamma0EisensteinScatteringInfinity_euler N hN s hs]
  ring

theorem gamma0EisensteinFourier_zero_euler (N : ℕ) (hN : 0<N) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    gamma0EisensteinFourierCoefficient N s y hy 0 = (y:ℂ)^s+
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        (riemannZeta (2*s-1)/riemannZeta (2*s))*(N:ℂ)^(1-2*s)*
          ∏ p ∈ N.primeFactors, ((1-(p:ℂ)⁻¹)/(1-(p:ℂ)^(-2*s))) := by
  rw [gamma0EisensteinFourier_zero,gamma0Eisenstein_infinity_constant_term_euler N hN s hs y hy]

end ArtinMatthews
