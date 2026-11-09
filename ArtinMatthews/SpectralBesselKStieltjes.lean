module

public import ArtinMatthews.SpectralStieltjesKMellin
public import ArtinMatthews.SpectralAntiKMellinEvaluation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Stieltjes transform of the imaginary-order Schläfli kernel. -/

namespace ArtinMatthews

open Set MeasureTheory OAI.CubicEisenstein

noncomputable section

def spectralStieltjesKClosed (r x : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (Real.cosh (Real.pi * r) : ℂ)) *
    ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (Complex.exp (x : ℂ) * schlafliBesselK ((r : ℂ) * Complex.I) x))

theorem spectralStieltjesKClosed_continuousAt (r : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (spectralStieltjesKClosed r) x := by
  unfold spectralStieltjesKClosed
  have hexp : Continuous (fun y : ℝ => Complex.exp (y : ℂ)) := by fun_prop
  have hp : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (-(1 / 2 : ℂ))) x :=
    Complex.continuousAt_ofReal_cpow_const x _ (Or.inr hx.ne')
  exact (hp.mul (hexp.continuousAt.mul
    (schlafliBesselK_hasDerivAt ((r : ℂ) * Complex.I) x hx).continuousAt)).const_mul _

private theorem stieltjes_mellin_ratio (p a b c h : ℂ) (hh : h ≠ 0) :
    p / h * (a * h / (b * c)) = p / c * (a / b) := by
  calc
    _ = (p / h * h) * (a / (b * c)) := by ring
    _ = _ := by
      rw [div_mul_cancel₀ _ hh]
      simp only [div_eq_mul_inv, mul_inv]
      ring

theorem spectralStieltjesKClosed_hasMellin (r : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) (hsh : s.re < 1) :
    HasMellin (spectralStieltjesKClosed r) s
      (((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
        mellin (fun y : ℝ => Complex.exp (-(y : ℂ)) *
          schlafliBesselK ((r : ℂ) * Complex.I) y) (s - 1 / 2)) := by
  have hs' : |((r : ℂ) * Complex.I).re| < (s - 1 / 2).re := by
    norm_num [Complex.mul_re, Complex.sub_re, Complex.div_re]
    linarith
  have hsh' : (s - 1 / 2).re < 1 / 2 := by
    norm_num [Complex.sub_re, Complex.div_re]
    linarith
  have hanti := spectralAntiK_hasMellin ((r : ℂ) * Complex.I) (s - 1 / 2) hs' hsh'
  have hdamp := spectralDampedK_hasMellin ((r : ℂ) * Complex.I) (s - 1 / 2) hs'
  have hshift : s + -(1 / 2 : ℂ) = s - 1 / 2 := (sub_eq_add_neg _ _).symm
  have hp : MellinConvergent (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) •
      (Complex.exp (x : ℂ) * schlafliBesselK ((r : ℂ) * Complex.I) x)) s :=
    MellinConvergent.cpow_smul.mpr (by simpa only [hshift] using hanti.1)
  constructor
  · change MellinConvergent (fun x : ℝ => ((Real.pi : ℂ) / (Real.cosh (Real.pi * r) : ℂ)) *
        ((x : ℂ) ^ (-(1 / 2 : ℂ)) *
          (Complex.exp (x : ℂ) * schlafliBesselK ((r : ℂ) * Complex.I) x))) s
    simpa only [smul_eq_mul] using
      hp.const_smul ((Real.pi : ℂ) / (Real.cosh (Real.pi * r) : ℂ))
  · change mellin (fun x : ℝ => ((Real.pi : ℂ) / (Real.cosh (Real.pi * r) : ℂ)) •
        ((x : ℂ) ^ (-(1 / 2 : ℂ)) •
          (Complex.exp (x : ℂ) * schlafliBesselK ((r : ℂ) * Complex.I) x))) s = _
    rw [mellin_const_smul, mellin_cpow_smul, hshift, hanti.2, hdamp.2]
    have hsin : Complex.cos ((Real.pi : ℂ) * (s - 1 / 2)) =
        Complex.sin ((Real.pi : ℂ) * s) := by
      rw [show (Real.pi : ℂ) * (s - 1 / 2) = (Real.pi : ℂ) * s - (Real.pi : ℂ) / 2 by ring,
        Complex.cos_sub_pi_div_two]
    have hcosh : Complex.cos ((Real.pi : ℂ) * ((r : ℂ) * Complex.I)) =
        (Real.cosh (Real.pi * r) : ℂ) := by
      rw [← mul_assoc, Complex.cos_mul_I, Complex.ofReal_cosh, Complex.ofReal_mul]
    simp only [smul_eq_mul, hsin, hcosh]
    exact stieltjes_mellin_ratio _ _ _ _ _
      (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')

theorem spectralStieltjesK_eq_closed (r : ℝ) {x : ℝ} (hx : 0 < x) :
    spectralStieltjesK r x = spectralStieltjesKClosed r x := by
  let σ : ℝ := 3 / 4
  have hlo (t : ℝ) : 1 / 2 < ((σ : ℂ) + t * Complex.I).re := by
    norm_num [σ, Complex.add_re, Complex.mul_re]
  have hhi (t : ℝ) : ((σ : ℂ) + t * Complex.I).re < 1 := by
    norm_num [σ, Complex.add_re, Complex.mul_re]
  exact spectral_mellin_unique (spectralStieltjesK r) (spectralStieltjesKClosed r) σ
    (fun t => (spectralStieltjesK_hasMellin r _ (hlo t) (hhi t)).1)
    (fun t => (spectralStieltjesKClosed_hasMellin r _ (hlo t) (hhi t)).1)
    (fun t => (spectralStieltjesK_hasMellin r _ (hlo t) (hhi t)).2.trans
      (spectralStieltjesKClosed_hasMellin r _ (hlo t) (hhi t)).2.symm)
    hx (spectralStieltjesK_continuousAt r hx) (spectralStieltjesKClosed_continuousAt r hx)

private theorem cpow_neg_half_eq_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt x : ℂ)⁻¹ := by
  rw [Complex.cpow_neg, Real.sqrt_eq_rpow, Complex.ofReal_cpow hx.le]
  norm_num

private theorem stieltjesKernel_sqrt_eq (r x : ℝ) {y : ℝ} (hy : 0 < y) :
    Complex.exp (-(y : ℂ)) * schlafliBesselK ((r : ℂ) * Complex.I) y /
      ((Real.sqrt y : ℂ) * ((y + x : ℝ) : ℂ)) =
      spectralStieltjesKWeight r y / ((y + x : ℝ) : ℂ) := by
  rw [spectralStieltjesKWeight, cpow_neg_half_eq_inv_sqrt hy]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem schlafliBesselK_stieltjes_integrable (r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun y : ℝ => Complex.exp (-(y : ℂ)) *
      schlafliBesselK ((r : ℂ) * Complex.I) y /
        ((Real.sqrt y : ℂ) * ((y + x : ℝ) : ℂ))) (Ioi (0 : ℝ)) := by
  apply (spectralStieltjesK_slice_integrable r hx).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact (stieltjesKernel_sqrt_eq r x hy).symm

theorem schlafliBesselK_stieltjes (r : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioi (0 : ℝ), Complex.exp (-(y : ℂ)) *
      schlafliBesselK ((r : ℂ) * Complex.I) y /
        ((Real.sqrt y : ℂ) * ((y + x : ℝ) : ℂ))) =
      (Real.pi : ℂ) * Complex.exp (x : ℂ) *
        schlafliBesselK ((r : ℂ) * Complex.I) x /
          ((Real.sqrt x : ℂ) * (Real.cosh (Real.pi * r) : ℂ)) := by
  calc
    _ = spectralStieltjesK r x := by
      unfold spectralStieltjesK
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact stieltjesKernel_sqrt_eq r x hy
    _ = spectralStieltjesKClosed r x := spectralStieltjesK_eq_closed r hx
    _ = _ := by
      rw [spectralStieltjesKClosed, cpow_neg_half_eq_inv_sqrt hx]
      simp only [div_eq_mul_inv, mul_inv]
      ring

end

end ArtinMatthews
