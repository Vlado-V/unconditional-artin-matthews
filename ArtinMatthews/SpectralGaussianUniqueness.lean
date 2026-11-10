module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import ArtinMatthews.ShiftedVoronoiLaplaceUniqueness
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Function.JacobianOneDim


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine removal of Gaussian testing for continuous positive-modulus
functions.  The exact X dX Jacobian reduces it to the proved Laplace
uniqueness theorem; no transform equality is used as a definition. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem spectral_positive_square_image : (fun X : ℝ => X^2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext u
  constructor
  · rintro ⟨X,hX,rfl⟩
    exact sq_pos_of_pos (show 0 < X from hX)
  · intro hu
    exact ⟨Real.sqrt u,Real.sqrt_pos.mpr hu,Real.sq_sqrt (le_of_lt hu)⟩

theorem spectral_positive_square_injOn : InjOn (fun X : ℝ => X^2) (Ioi (0 : ℝ)) := by
  intro X hX Y hY hsq
  change 0 < X at hX
  change 0 < Y at hY
  nlinarith

theorem spectral_positive_square_integral (F : ℝ → ℂ) :
    (∫ u in Ioi (0 : ℝ), F u) = ∫ X in Ioi (0 : ℝ), (2*X : ℝ) • F (X^2) := by
  conv_lhs => rw [← spectral_positive_square_image]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      (fun X _ => (show HasDerivAt (fun u : ℝ => u^2) (2*X) X by
        simpa using! (hasDerivAt_id X).pow 2).hasDerivWithinAt)
      spectral_positive_square_injOn]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [abs_of_pos (mul_pos two_pos hX)]

theorem spectral_positive_square_integrable (F : ℝ → ℂ) :
    IntegrableOn F (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun X : ℝ => (2*X : ℝ) • F (X^2)) (Ioi (0 : ℝ)) := by
  conv_lhs => rw [← spectral_positive_square_image]
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      (fun X _ => (show HasDerivAt (fun u : ℝ => u^2) (2*X) X by
        simpa using! (hasDerivAt_id X).pow 2).hasDerivWithinAt)
      spectral_positive_square_injOn]
  apply integrableOn_congr_fun
  · intro X hX
    dsimp only
    rw [abs_of_pos (mul_pos two_pos hX)]
  · exact measurableSet_Ioi

theorem spectral_gaussian_to_laplace_integrable (f : ℝ → ℂ) (p : ℝ)
    (hi : IntegrableOn (fun X : ℝ => Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*f X)
      (Ioi (0 : ℝ))) :
    IntegrableOn (fun u : ℝ => f (Real.sqrt u)*Complex.exp (-(p*u : ℝ))) (Ioi (0 : ℝ)) := by
  apply (spectral_positive_square_integrable _).mpr
  apply (hi.const_mul (2 : ℂ)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  rw [Complex.real_smul,Real.sqrt_sq (le_of_lt hX)]
  push_cast
  ring_nf

theorem spectral_gaussian_to_laplace_integral (f : ℝ → ℂ) (p : ℝ) :
    (∫ u in Ioi (0 : ℝ), f (Real.sqrt u)*Complex.exp (-(p*u : ℝ))) =
      2*(∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*f X) := by
  rw [spectral_positive_square_integral,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro X hX
  dsimp only
  rw [Complex.real_smul,Real.sqrt_sq (le_of_lt hX)]
  push_cast
  ring_nf

theorem spectral_eqOn_Ioi_of_gaussian_eq (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ioi (0 : ℝ))) (hg : ContinuousOn g (Ioi (0 : ℝ))) (S : ℝ)
    (hfi : ∀ p : ℝ, S < p → IntegrableOn (fun X : ℝ =>
      Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*f X) (Ioi (0 : ℝ)))
    (hgi : ∀ p : ℝ, S < p → IntegrableOn (fun X : ℝ =>
      Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*g X) (Ioi (0 : ℝ)))
    (heq : ∀ p : ℝ, S < p →
      (∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*f X) =
        ∫ X in Ioi (0 : ℝ), Complex.exp (-(p : ℂ)*(X : ℂ)^2)*(X : ℂ)*g X) :
    EqOn f g (Ioi (0 : ℝ)) := by
  have hsqrt : MapsTo Real.sqrt (Ioi (0 : ℝ)) (Ioi (0 : ℝ)) := fun u hu => Real.sqrt_pos.mpr hu
  have h := eqOn_Ioi_of_laplace_eq (fun u => f (Real.sqrt u)) (fun u => g (Real.sqrt u))
    (hf.comp Real.continuous_sqrt.continuousOn hsqrt)
    (hg.comp Real.continuous_sqrt.continuousOn hsqrt) S
    (fun p hp => spectral_gaussian_to_laplace_integrable f p (hfi p hp))
    (fun p hp => spectral_gaussian_to_laplace_integrable g p (hgi p hp)) (by
      intro p hp
      rw [spectral_gaussian_to_laplace_integral,spectral_gaussian_to_laplace_integral,heq p hp])
  intro X hX
  have hh := h (show X^2 ∈ Ioi (0 : ℝ) from sq_pos_of_pos (show 0 < X from hX))
  simpa only [Real.sqrt_sq (le_of_lt hX)] using hh

end ArtinMatthews
