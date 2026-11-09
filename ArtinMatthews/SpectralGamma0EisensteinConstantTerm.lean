module

public import ArtinMatthews.SpectralGamma0EisensteinTotientIntegral
public import ArtinMatthews.SpectralGamma0EisensteinTotientSeries


set_option backward.privateInPublic true
@[expose] public section

/-! The actual infinity-cusp constant term in the absolute-convergence half-plane. -/
noncomputable section
open Set MeasureTheory
namespace ArtinMatthews

def gamma0EisensteinScatteringInfinity (N : ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*gamma0EisensteinTotientSeries N s

theorem gamma0EisensteinCoordinateIntegral_summable (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    Summable (fun v : Gamma0EisensteinPositiveCoordinates N =>
      gamma0EisensteinCoordinateIntegral N s y hy v.1 v.2) := by
  have h := (gamma0EisensteinPositiveCoordinateEquiv N).summable_iff.mpr
    (gamma0EisensteinPositiveTerm_integral_summable N s hs y hy)
  exact h

theorem gamma0Eisenstein_positive_integral_totient_sum (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∑' v : Gamma0EisensteinPositiveRows N, ∫ x in Ioc (0:ℝ) 1,
      gamma0EisensteinPrimitiveTerm N s v.val (gamma0EisensteinHorizontalPoint y hy x)) =
      (y:ℂ)^(1-s)*gamma0EisensteinScatteringInfinity N s := by
  let f : Gamma0EisensteinPositiveRows N → ℂ := fun v => ∫ x in Ioc (0:ℝ) 1,
    gamma0EisensteinPrimitiveTerm N s v.val (gamma0EisensteinHorizontalPoint y hy x)
  let e := gamma0EisensteinPositiveCoordinateEquiv N
  have hsum := gamma0EisensteinCoordinateIntegral_summable N s hs y hy
  have hsigma := Summable.tsum_sigma
    (f := fun v : Gamma0EisensteinPositiveCoordinates N =>
      gamma0EisensteinCoordinateIntegral N s y hy v.1 v.2) hsum
  change (∑' v, f v)=_
  rw [← e.tsum_eq f]
  change (∑' v : Gamma0EisensteinPositiveCoordinates N,
    gamma0EisensteinCoordinateIntegral N s y hy v.1 v.2)=_
  rw [hsigma]
  have hinner (c : Gamma0EisensteinPositiveFirst N) :
      (∑' d, gamma0EisensteinCoordinateIntegral N s y hy c d) =
        (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s)*(y:ℂ)^(1-s)*
          ((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s) :=
    gamma0EisensteinCoordinateIntegral_tsum N s hs y hy c (hsum.sigma_factor c)
  simp_rw [hinner]
  rw [tsum_mul_right,tsum_mul_right,gamma0EisensteinTotientSeries_eq_positive_first]
  unfold gamma0EisensteinScatteringInfinity
  ring

theorem gamma0Eisenstein_infinity_constant_term (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) =
      (y:ℂ)^s+(y:ℂ)^(1-s)*gamma0EisensteinScatteringInfinity N s := by
  rw [gamma0Eisenstein_integral_eq_positive_rows N s hs y hy,
    gamma0Eisenstein_positive_integral_totient_sum N s hs y hy]

theorem gamma0EisensteinFourier_zero_scattering (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    gamma0EisensteinFourierCoefficient N s y hy 0 =
      (y:ℂ)^s+(y:ℂ)^(1-s)*gamma0EisensteinScatteringInfinity N s := by
  rw [gamma0EisensteinFourier_zero,gamma0Eisenstein_infinity_constant_term N s hs y hy]

theorem gamma0Eisenstein_infinity_constant_term_explicit (N : ℕ) (s : ℂ) (hs : 1<s.re)
    (y : ℝ) (hy : 0<y) :
    (∫ x in (0:ℝ)..1, gamma0EisensteinSlice N s y hy x) = (y:ℂ)^s+
      (y:ℂ)^(1-s)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (s-1/2)/Complex.Gamma s)*
        ∑' c : {c : ℕ // 0<c ∧ N∣c}, (c.val.totient:ℂ)*(c.val:ℂ)^(-2*s) := by
  rw [gamma0Eisenstein_infinity_constant_term N s hs y hy]
  unfold gamma0EisensteinScatteringInfinity gamma0EisensteinTotientSeries
  ring

end ArtinMatthews
