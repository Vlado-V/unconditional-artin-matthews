module

public import ArtinMatthews.SpectralBesselPoissonSeries
public import ArtinMatthews.SpectralKLRealKernel
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.MeasureTheory.Constructions.Polish.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Joint measurability of the actual imaginary-order Bessel kernels.
The positive-argument extension is proved from the defining J series and
the actual cosh K integral, rather than assumed as a transform hypothesis. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace ArtinMatthews

theorem spectral_Gamma_imaginary_shift_continuous (a : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => Complex.Gamma (((a*t : ℝ) : ℂ)*Complex.I+1+n)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hre : 0 < ((((a*t : ℝ) : ℂ)*Complex.I+1+n) : ℂ).re := by
    norm_num only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.one_re, zero_add, Complex.natCast_re]
    positivity
  have harg : ContinuousAt (fun u : ℝ => ((a*u : ℝ) : ℂ)*Complex.I+1+(n : ℂ)) t := by fun_prop
  exact (Complex.hasDerivAt_Gamma_of_re_pos hre).continuousAt.comp (f := fun u : ℝ => ((a*u : ℝ) : ℂ)*Complex.I+1+(n : ℂ)) harg

theorem spectral_besselImaginaryPower_positive_measurable (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => if 0 < p.2 then (p.2/2 : ℂ)^(((a*p.1 : ℝ) : ℂ)*Complex.I) else 0) := by
  let S : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_snd).measurableSet
  have hc : ContinuousOn (fun p : ℝ × ℝ => (p.2/2 : ℂ)^(((a*p.1 : ℝ) : ℂ)*Complex.I)) S := by
    apply ContinuousOn.cpow (by fun_prop) (by fun_prop)
    intro p hp
    have hp0 : 0 < p.2/2 := half_pos hp
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using Complex.ofReal_mem_slitPlane.mpr hp0
  exact hc.measurable_piecewise continuousOn_const hS

theorem spectral_besselJ_imaginary_positive_joint_measurable (a : ℝ) :
    Measurable (fun p : ℝ × ℝ => if 0 < p.2 then
      Complex.besselJ (((a*p.1 : ℝ) : ℂ)*Complex.I) (p.2 : ℂ) else 0) := by
  let T : ℕ → (ℝ × ℝ) → ℂ := fun n p => (-(p.2/2 : ℂ)^2)^n/
    ((n.factorial : ℂ)*Complex.Gamma (((a*p.1 : ℝ) : ℂ)*Complex.I+1+n))
  have hm (n : ℕ) : Measurable (T n) := by
    have hG : Measurable (fun p : ℝ × ℝ => Complex.Gamma (((a*p.1 : ℝ) : ℂ)*Complex.I+1+n)) :=
      (spectral_Gamma_imaginary_shift_continuous a n).measurable.comp measurable_fst
    unfold T
    exact (by fun_prop : Measurable (fun p : ℝ × ℝ => (-(p.2/2 : ℂ)^2)^n)).div
      (measurable_const.mul hG)
  have hs : Measurable (fun p : ℝ × ℝ => ∑' n : ℕ, T n p) := Measurable.tsum hm
  have hprod := (spectral_besselImaginaryPower_positive_measurable a).mul hs
  have he : (fun p : ℝ × ℝ => if 0 < p.2 then
      Complex.besselJ (((a*p.1 : ℝ) : ℂ)*Complex.I) (p.2 : ℂ) else 0) =
      (fun p : ℝ × ℝ => if 0 < p.2 then (p.2/2 : ℂ)^(((a*p.1 : ℝ) : ℂ)*Complex.I) else 0) *
      (fun p : ℝ × ℝ => ∑' n : ℕ, T n p) := by
    funext p
    dsimp only [Pi.mul_apply]
    by_cases hp : 0 < p.2
    · rw [ite_eq_left hp,ite_eq_left hp,besselJ_eq_hypergeometric_tsum]
    · simp only [ite_eq_right hp,zero_mul]
  rw [he]
  exact hprod

theorem spectral_besselK_imaginary_positive_joint_measurable :
    Measurable (fun p : ℝ × ℝ => if 0 < p.2 then
      OAI.CubicEisenstein.schlafliBesselK ((p.1 : ℂ)*Complex.I) p.2 else 0) := by
  have hm : Measurable (fun p : ℝ × ℝ => if 0 < p.2 then
      (spectralKLRealKernel p.1 p.2 : ℂ) else 0) := by
    apply Measurable.ite (show MeasurableSet {p : ℝ × ℝ | 0 < p.2} from (isOpen_lt continuous_const continuous_snd).measurableSet)
    · exact Complex.continuous_ofReal.measurable.comp spectralKLRealKernel_stronglyMeasurable.measurable
    · exact measurable_const
  have he : (fun p : ℝ × ℝ => if 0 < p.2 then
      OAI.CubicEisenstein.schlafliBesselK ((p.1 : ℂ)*Complex.I) p.2 else 0) =
      (fun p : ℝ × ℝ => if 0 < p.2 then (spectralKLRealKernel p.1 p.2 : ℂ) else 0) := by
    funext p
    by_cases hp : 0 < p.2
    · rw [ite_eq_left hp,ite_eq_left hp]
      exact schlafliBesselK_imaginary_eq_realKernel p.1 hp
    · simp only [ite_eq_right hp]
  rw [he]
  exact hm

end ArtinMatthews
