module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.SpectralGaussianUniqueness
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set MeasureTheory
noncomputable section

private theorem gaussian_plain_div_eq (f : ℝ → ℂ) (p x : ℝ) (hx : 0 < x) :
    Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) *
      (f x / (x : ℂ)) = Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x := by
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

theorem spectral_eqOn_Ioi_of_plain_gaussian_eq (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi (0 : ℝ))) (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (S : ℝ)
    (hfi : ∀ p : ℝ, S < p → IntegrableOn
      (fun x : ℝ => Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x) (Ioi (0 : ℝ)))
    (hgi : ∀ p : ℝ, S < p → IntegrableOn
      (fun x : ℝ => Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * g x) (Ioi (0 : ℝ)))
    (heq : ∀ p : ℝ, S < p →
      (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * f x) =
      ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * g x) :
    EqOn f g (Ioi (0 : ℝ)) := by
  have hdiv (h : ℝ → ℂ) (hh : ContinuousOn h (Ioi (0 : ℝ))) :
      ContinuousOn (fun x : ℝ => h x / (x : ℂ)) (Ioi (0 : ℝ)) :=
    hh.div Complex.continuous_ofReal.continuousOn
      (fun x hx => Complex.ofReal_ne_zero.mpr hx.ne')
  have hi (h : ℝ → ℂ) (p : ℝ)
      (hh : IntegrableOn (fun x : ℝ =>
        Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * h x) (Ioi (0 : ℝ))) :
      IntegrableOn (fun x : ℝ =>
        Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) *
          (h x / (x : ℂ))) (Ioi (0 : ℝ)) := by
    apply hh.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (gaussian_plain_div_eq h p x hx).symm
  have he (h : ℝ → ℂ) (p : ℝ) :
      (∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) *
        (x : ℂ) * (h x / (x : ℂ))) =
      ∫ x in Ioi (0 : ℝ), Complex.exp (-(p : ℂ) * (x : ℂ) ^ 2) * h x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact gaussian_plain_div_eq h p x hx
  have h := spectral_eqOn_Ioi_of_gaussian_eq
    (fun x : ℝ => f x / (x : ℂ)) (fun x : ℝ => g x / (x : ℂ))
    (hdiv f hf) (hdiv g hg) S
    (fun p hp => hi f p (hfi p hp)) (fun p hp => hi g p (hgi p hp))
    (by intro p hp; rw [he f p, he g p]; exact heq p hp)
  intro x hx
  exact (div_left_inj' (Complex.ofReal_ne_zero.mpr hx.ne')).mp (h hx)

end
end ArtinMatthews
