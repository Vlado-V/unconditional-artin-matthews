module

public import ArtinMatthews.SpectralBesselLegendreTransform
public import ArtinMatthews.SpectralJGaussianProbe


set_option backward.privateInPublic true
@[expose] public section

/-! The exact Gaussian calibration of the odd Bessel functions through
the checked order-zero probe and shifted Legendre coefficient. -/
namespace ArtinMatthews
open Complex MeasureTheory Set
open scoped Interval

noncomputable section

private def spectralLegendreGaussianIntegrand (n : ℕ) (p : ℝ) (z : ℝ × ℝ) : ℂ :=
  (spectralLegendreValue n z.2 : ℂ) *
    (spectralJGaussianProbe p z.1 * spectralJGaussianKernel z.1 (2*z.2))

private theorem spectralLegendreGaussianIntegrand_continuous (n : ℕ) (p : ℝ) :
    Continuous (spectralLegendreGaussianIntegrand n p) := by
  have hL : Continuous (fun z : ℝ × ℝ => (spectralLegendreValue n z.2 : ℂ)) :=
    Complex.continuous_ofReal.comp ((spectralLegendreValue_continuous n).comp continuous_snd)
  have hprobe : Continuous (fun z : ℝ × ℝ => spectralJGaussianProbe p z.1) :=
    (spectralJGaussianProbe_continuous p).comp continuous_fst
  have hscale : Continuous (fun z : ℝ × ℝ => (2 : ℝ)*z.2) :=
    continuous_const.mul continuous_snd
  have hpair : Continuous (fun z : ℝ × ℝ => (z.1,(2 : ℝ)*z.2)) :=
    continuous_fst.prodMk hscale
  have hkernel : Continuous (fun z : ℝ × ℝ => spectralJGaussianKernel z.1 (2*z.2)) := by
    simpa only [Function.comp_def] using spectralJGaussianKernel_continuous.comp hpair
  exact hL.mul (hprobe.mul hkernel)

private theorem spectralLegendreGaussianIntegrand_norm_le (n : ℕ) (p M C : ℝ)
    (hM : 0 ≤ M)
    (hP : ∀ u ∈ Icc (0 : ℝ) 1, ‖spectralLegendreValue n u‖ ≤ M)
    (hK : ∀ x w : ℝ, ‖spectralJGaussianKernel x w‖ ≤ C)
    (z : ℝ × ℝ) (hz : z.2 ∈ Ioc (0 : ℝ) 1) :
    ‖spectralLegendreGaussianIntegrand n p z‖ ≤ ‖spectralJGaussianProbe p z.1‖ * (M*C) := by
  have hZ : ‖spectralLegendreValue n z.2‖ ≤ M := hP z.2 ⟨hz.1.le,hz.2⟩
  simp only [spectralLegendreGaussianIntegrand, norm_mul, Complex.norm_real]
  calc
    _ ≤ M * (‖spectralJGaussianProbe p z.1‖ * C) :=
      mul_le_mul hZ (mul_le_mul_of_nonneg_left (hK z.1 (2*z.2)) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hM
    _ = _ := by ring

private theorem spectralLegendreGaussianIntegrand_integrable (n : ℕ) (p : ℝ) (hp : 0 < p) :
    Integrable (spectralLegendreGaussianIntegrand n p)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (Ioc (0 : ℝ) 1) univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  obtain ⟨M,hM,hP⟩ := spectralLegendreValue_unit_bound n
  obtain ⟨C,hC,hK⟩ := spectralJGaussianKernel_bound
  have hprobe : Integrable (spectralJGaussianProbe p) μ :=
    spectralJGaussianProbe_integrable p hp
  have hconst : Integrable (fun _ : ℝ => M*C) ν := integrable_const (M*C)
  have hdom : Integrable (fun z : ℝ × ℝ => ‖spectralJGaussianProbe p z.1‖ * (M*C)) (μ.prod ν) :=
    hprobe.norm.mul_prod hconst
  have hF : AEStronglyMeasurable (spectralLegendreGaussianIntegrand n p) (μ.prod ν) :=
    (spectralLegendreGaussianIntegrand_continuous n p).aestronglyMeasurable
  have ha : ∀ᵐ u ∂ν, u ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
  have hs : Measure.QuasiMeasurePreserving (Prod.snd : ℝ × ℝ → ℝ) (μ.prod ν) ν :=
    Measure.quasiMeasurePreserving_snd
  change Integrable (spectralLegendreGaussianIntegrand n p) (μ.prod ν)
  apply hdom.mono' hF
  filter_upwards [hs.ae ha] with z hz
  exact spectralLegendreGaussianIntegrand_norm_le n p M C hM hP hK z hz

private def spectralBesselOddGaussianIntegrand (n : ℕ) (p x : ℝ) : ℂ :=
  (Real.exp (-(p*x^2)) : ℂ) * Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ)

private theorem spectralLegendreGaussianIntegrand_row (n : ℕ) (p x : ℝ) (hx : 0 < x) :
    (∫ u in Ioc (0 : ℝ) 1, spectralLegendreGaussianIntegrand n p (x,u)) =
      2 * spectralBesselOddGaussianIntegrand n p x := by
  have hK (u : ℝ) : spectralJGaussianKernel x (2*u) =
      Complex.besselJ 0 ((x : ℂ) * Real.sqrt u) := by
    unfold spectralJGaussianKernel
    rw [spectral_besselJ_zero_sqrt_argument x u hx.le,
      show (x^2/8)*(2*u) = (x/2)^2*u by ring]
  have hrow :
      (∫ u in Ioc (0 : ℝ) 1, spectralLegendreGaussianIntegrand n p (x,u)) =
      spectralJGaussianProbe p x *
        (∫ u in (0 : ℝ)..1, (spectralLegendreValue n u : ℂ) *
          Complex.besselJ 0 ((x : ℂ) * (Real.sqrt u : ℂ))) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro u _
    simp only [spectralLegendreGaussianIntegrand, hK]
    ring
  rw [hrow, spectral_shiftedLegendre_besselJ_zero n x hx, spectralJGaussianProbe,
    spectralBesselOddGaussianIntegrand]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp <;> ring

private theorem spectralLegendreGaussianIntegrand_column (n : ℕ) (p u : ℝ)
    (hp : 0 < p) (hu : 0 ≤ u) :
    (∫ x in Ioi (0 : ℝ), spectralLegendreGaussianIntegrand n p (x,u)) =
      ((1 / (2*p) : ℝ) : ℂ) *
        ((spectralLegendreValue n u : ℂ) * (Real.exp (-u/(4*p)) : ℂ)) := by
  have hcol :
      (∫ x in Ioi (0 : ℝ), spectralLegendreGaussianIntegrand n p (x,u)) =
      (spectralLegendreValue n u : ℂ) *
        spectralJGaussianTransform (spectralJGaussianProbe p) (2*u) := by
    unfold spectralJGaussianTransform
    rw [← integral_const_mul]
    rfl
  rw [hcol, spectralJGaussianProbe_transform p (2*u) hp (by positivity),
    show -(2*u)/(8*p) = -u/(4*p) by ring]
  push_cast
  ring

theorem spectral_besselJ_odd_gaussian (n : ℕ) (p : ℝ) (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => (Real.exp (-(p*x^2)) : ℂ) *
      Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ)) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), (Real.exp (-(p*x^2)) : ℂ) *
        Complex.besselJ ((2*n+1 : ℕ) : ℂ) (x : ℂ)) =
      ((1/(4*p) : ℝ) : ℂ) * (∫ u in (0 : ℝ)..1,
        (spectralLegendreValue n u : ℂ) * (Real.exp (-u/(4*p)) : ℂ)) := by
  let f := spectralBesselOddGaussianIntegrand n p
  let F := spectralLegendreGaussianIntegrand n p
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have hF : Integrable F (μ.prod ν) := spectralLegendreGaussianIntegrand_integrable n p hp
  change Integrable f μ ∧ (∫ x, f x ∂μ) =
    ((1/(4*p) : ℝ) : ℂ) * (∫ u in (0 : ℝ)..1,
      (spectralLegendreValue n u : ℂ) * (Real.exp (-u/(4*p)) : ℂ))
  constructor
  · have hI := hF.integral_prod_left.const_mul (1/2 : ℂ)
    apply hI.congr
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))]
      with x hx
    change (1/2 : ℂ) * (∫ u in Ioc (0 : ℝ) 1, F (x,u)) = f x
    rw [spectralLegendreGaussianIntegrand_row n p x hx]
    ring
  · apply (mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0))
    have hFub := (integral_prod F hF).symm.trans (integral_prod_symm F hF)
    calc
      _ = ∫ x, (2 : ℂ) * f x ∂μ := (integral_const_mul 2 f).symm
      _ = ∫ x, ∫ u, F (x,u) ∂ν ∂μ :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun x hx => (spectralLegendreGaussianIntegrand_row n p x hx).symm)
      _ = ∫ u, ∫ x, F (x,u) ∂μ ∂ν := hFub
      _ = ∫ u, ((1 / (2*p) : ℝ) : ℂ) *
          ((spectralLegendreValue n u : ℂ) * (Real.exp (-u/(4*p)) : ℂ)) ∂ν :=
        setIntegral_congr_fun measurableSet_Ioc
          (fun u hu => spectralLegendreGaussianIntegrand_column n p u hp hu.1.le)
      _ = _ := by
        rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
        have hc : ((1 / (2*p) : ℝ) : ℂ) = 2 * ((1 / (4*p) : ℝ) : ℂ) := by
          push_cast
          have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
          field_simp <;> ring
        rw [hc,mul_assoc]

end
end ArtinMatthews
