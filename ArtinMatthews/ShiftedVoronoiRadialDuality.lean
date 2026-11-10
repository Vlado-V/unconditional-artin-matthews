module

public import OAI.NumberTheory.DirichletL.GaussSum.SexticRadialPoisson
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import OAI.NumberTheory.DirichletL.Poisson.RadialFourier


set_option backward.privateInPublic true
@[expose] public section

/-!
# Laplace duality for the actual radial Fourier transform

These proofs adapt the genuinely proved Gaussian-pairing argument from
`OAI/NumberTheory/DirichletL/Detector/RadialMellin.lean`, without importing its
unfinished umbrella dependency `DirichletL.Foundation`. The radial change of
variables is the proof from `DirichletL/Eisenstein/HyperbolicSpace.lean`.

The operator is OAI's actual Schwartz Fourier transform `paperRadialFourier`;
no transform identity is supplied as a hypothesis.
-/

noncomputable section

open MeasureTheory Set Filter
open OAI.EisensteinSchwartzPoisson
open scoped FourierTransform RealInnerProductSpace

namespace ArtinMatthews

/-- The half-line Laplace transform, in the multiplication order used below. -/
def radialLaplace (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, f r * Complex.exp (-(t * r : ℝ))

/-- The scale of OAI's Eisenstein-normalized radial Fourier transform. -/
def radialFourierConstant : ℝ := 2 * Real.pi / Real.sqrt 3

theorem radialFourierConstant_pos : 0 < radialFourierConstant := by
  unfold radialFourierConstant
  positivity

theorem radialFourierConstant_sq : radialFourierConstant ^ 2 = 4 * Real.pi ^ 2 / 3 := by
  unfold radialFourierConstant
  rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

private theorem integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r ^ 2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul] at hpolar hsub
  rw [hpolar, ← hsub]
  rw [show (fun x : ℝ => (2 : ℂ) * x * f (x ^ 2)) =
      (fun x : ℝ => (2 : ℂ) * (x * f (x ^ 2))) by funext x; ring, integral_const_mul]
  ring

private theorem radial_paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp

private theorem radial_paper_fourier_pairing (f g : ℂ → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ u : ℂ, paperFourier f u * g u) = ∫ z : ℂ, f z * paperFourier g z := by
  have hi : Integrable (fun p : ℂ × ℂ => paperE (-(p.2 * p.1)) * f p.2 * g p.1) := by
    apply (hg.norm.mul_prod hf.norm).mono'
    · have hp : Continuous (fun p : ℂ × ℂ => paperE (-(p.2 * p.1))) := by
        simp_rw [paperE_eq_exp]
        fun_prop
      exact (hp.aestronglyMeasurable.mul hf.aestronglyMeasurable.comp_snd).mul
        hg.aestronglyMeasurable.comp_fst
    · exact Eventually.of_forall fun p => by
        simp only [norm_mul, radial_paperE_norm, one_mul]
        exact le_of_eq (mul_comm _ _)
  simp only [paperFourier, Complex.real_smul]
  simp_rw [mul_assoc, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (hi.const_mul ((2 / Real.sqrt 3 : ℝ) : ℂ))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by dsimp only; rw [mul_comm z u]; ring

private theorem radial_paper_gaussian_fourier (t : ℝ) (ht : 0 < t) (u : ℂ) :
    paperFourier (fun z : ℂ => Complex.exp (-(t : ℂ) * ‖z‖ ^ 2)) u =
      (radialFourierConstant / t : ℝ) *
        Complex.exp (-(radialFourierConstant ^ 2 * ‖u‖ ^ 2 / t : ℝ)) := by
  rw [paperFourier_eq_standard,
    fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat,
    div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  simp only [Complex.real_smul, ← Complex.ofReal_pow, paperFrequency_norm_sq,
    radialFourierConstant_sq]
  push_cast
  have he : -(Real.pi : ℂ) ^ 2 * ((4 / 3 : ℝ) * ‖u‖ ^ 2 : ℝ) / (t : ℂ) =
      -((4 * Real.pi ^ 2 / 3 * ‖u‖ ^ 2 / t : ℝ) : ℂ) := by push_cast; ring
  push_cast at he
  rw [he]
  unfold radialFourierConstant
  push_cast
  ring

/-- Gaussian Fourier pairing gives the Laplace duality of the actual radial
Fourier transform. All source functions are genuine Schwartz functions. -/
theorem radial_laplace_duality (W : SchwartzMap ℝ ℂ) (t : ℝ) (ht : 0 < t) :
    radialLaplace (paperRadialFourier W) t =
      (radialFourierConstant / t : ℝ) *
        radialLaplace W (radialFourierConstant ^ 2 / t) := by
  have hf : Integrable (fun z : ℂ => W (‖z‖ ^ 2)) := (radialTestCLM W).integrable
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ) * ‖z‖ ^ 2)) := by
    simpa only [zero_mul, add_zero] using
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa using ht) 0 (0 : ℂ)
  have h := radial_paper_fourier_pairing _ _ hf hg
  have hleft : (∫ u : ℂ, paperFourier (fun z : ℂ => W (‖z‖ ^ 2)) u *
      Complex.exp (-(t : ℂ) * ‖u‖ ^ 2)) =
        (Real.pi : ℂ) * radialLaplace (paperRadialFourier W) t := by
    simp_rw [paperFourier_radial]
    rw [radialLaplace, ← integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by simp [Complex.ofReal_mul]
  have hright : (∫ z : ℂ, W (‖z‖ ^ 2) * paperFourier
      (fun u : ℂ => Complex.exp (-(t : ℂ) * ‖u‖ ^ 2)) z) =
      (Real.pi : ℂ) * ((radialFourierConstant / t : ℝ) *
        radialLaplace W (radialFourierConstant ^ 2 / t)) := by
    simp_rw [radial_paper_gaussian_fourier t ht]
    rw [radialLaplace, ← integral_const_mul, ← integral_radial_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      dsimp only
      have he : radialFourierConstant ^ 2 * ‖u‖ ^ 2 / t =
          radialFourierConstant ^ 2 / t * ‖u‖ ^ 2 := by ring
      rw [he]
      ring
  rw [hleft, hright] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h

end ArtinMatthews
