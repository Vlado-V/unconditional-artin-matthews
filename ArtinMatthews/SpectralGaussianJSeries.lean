module

public import ArtinMatthews.SpectralGaussianGammaIntegrability
public import ArtinMatthews.SpectralBetaExponentialGamma


set_option backward.privateInPublic true
@[expose] public section

/-! The actual defining J series inside a Gaussian, matched term by term
to the proved absolutely integrable gamma series. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators

namespace ArtinMatthews

theorem spectralGaussianJ_series (ν : ℂ) {q x : ℝ} (hq : 0 < q) (hx : 0 < x) :
    Complex.exp (-(x : ℂ)^2)*Complex.besselJ (2*ν) ((q : ℂ)*(x : ℂ)) =
      (q/2 : ℂ)^(2*ν)*
        ∑' n : ℕ, spectralGaussianGammaTerm (ν+1/2) (2*ν+1) (-(q/2 : ℂ)^2) n x := by
  let z : ℂ := -(q/2 : ℂ)^2
  let D : ℕ → ℂ := fun n => (z*(x : ℂ)^2)^n/
    ((n.factorial : ℂ)*Complex.Gamma (2*ν+1+n))
  have ht (n : ℕ) : spectralGaussianGammaTerm (ν+1/2) (2*ν+1) z n x =
      ((x : ℂ)^(2*ν)*Complex.exp (-(x : ℂ)^2))*D n := by
    unfold spectralGaussianGammaTerm D
    rw [show 2*((ν+(1/2 : ℂ))+n)-1 = 2*ν+2*n by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
    have hxn : (x : ℂ)^(2*(n : ℂ)) = ((x : ℂ)^2)^n := by
      have h := Complex.cpow_nat_mul (x : ℂ) n (2 : ℂ)
      rw [Complex.cpow_two] at h
      simpa only [mul_comm] using h
    rw [hxn,mul_pow]
    ring_nf
  have hsum : (∑' n : ℕ, spectralGaussianGammaTerm (ν+1/2) (2*ν+1) z n x) =
      ((x : ℂ)^(2*ν)*Complex.exp (-(x : ℂ)^2))*∑' n : ℕ, D n := by
    simp_rw [ht]
    exact tsum_mul_left
  have hp : (((q : ℂ)*(x : ℂ))/2)^(2*ν) = (q/2 : ℂ)^(2*ν)*(x : ℂ)^(2*ν) := by
    have h := Complex.mul_cpow_ofReal_nonneg (a := q/2) (b := x)
      (half_pos hq).le hx.le (2*ν)
    convert h using 1 <;> push_cast <;> ring_nf
  have hz : -(((q : ℂ)*(x : ℂ))/2)^2 = z*(x : ℂ)^2 := by dsimp [z]; ring_nf
  rw [besselJ_eq_hypergeometric_tsum,hp,hz]
  change _ = (q/2 : ℂ)^(2*ν)*∑' n : ℕ, spectralGaussianGammaTerm (ν+1/2) (2*ν+1) z n x
  rw [hsum]
  change Complex.exp (-(x : ℂ)^2)*((q/2 : ℂ)^(2*ν)*(x : ℂ)^(2*ν)*∑' n : ℕ, D n) = _
  ring_nf

theorem spectralGaussianJ_integrable (ν : ℂ) (hν : -(1/2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun x : ℝ => Complex.exp (-(x : ℂ)^2)*Complex.besselJ (2*ν) ((q : ℂ)*(x : ℂ)))
      (Ioi (0 : ℝ)) := by
  have ha : 0 < (ν+(1/2 : ℂ)).re := by norm_num; linarith
  have hi := (spectralGaussianGammaSeries_integrable (ν+1/2) (2*ν+1) (-(q/2 : ℂ)^2) ha).const_mul
    ((q/2 : ℂ)^(2*ν))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (spectralGaussianJ_series ν hq hx).symm

theorem spectralGaussianJ_gamma_integral (ν : ℂ) (hν : -(1/2 : ℝ) < ν.re)
    {q : ℝ} (hq : 0 < q) :
    (∫ x in Ioi (0 : ℝ), Complex.exp (-(x : ℂ)^2)*Complex.besselJ (2*ν) ((q : ℂ)*(x : ℂ))) =
      (q/2 : ℂ)^(2*ν)*(1/2 : ℂ)*
        ∑' n : ℕ, Complex.Gamma (ν+1/2+n)*(-(q/2 : ℂ)^2)^n/
          ((n.factorial : ℂ)*Complex.Gamma (2*ν+1+n)) := by
  have ha : 0 < (ν+(1/2 : ℂ)).re := by norm_num; linarith
  calc
    _ = (q/2 : ℂ)^(2*ν)*∫ x in Ioi (0 : ℝ),
        ∑' n : ℕ, spectralGaussianGammaTerm (ν+1/2) (2*ν+1) (-(q/2 : ℂ)^2) n x := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact spectralGaussianJ_series ν hq hx
    _ = _ := by rw [spectralGaussianGammaSeries_integral _ _ _ ha]; ring_nf

end ArtinMatthews
