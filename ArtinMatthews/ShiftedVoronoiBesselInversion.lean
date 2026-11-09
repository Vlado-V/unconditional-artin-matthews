module

public import ArtinMatthews.ShiftedVoronoiBesselMellin
public import ArtinMatthews.ShiftedVoronoiNormalizedInversion
public import ArtinMatthews.ShiftedVoronoiBesselTransform


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin inversion of the actual weight-one Bessel transform

For compact smooth sources away from zero, the inverse Mellin representation
is proved with convergence discharged. This is the analytic Bessel inversion
step; the shifted coefficient summation and spectral estimate are separate.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

theorem besselZeroTransform_mellin_inversion
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hx : 0 < x) :
    mellinInv σ (mellin (besselZeroTransform W)) x = besselZeroTransform W x := by
  rw [mellin_besselZeroTransform_eq_normalizedRadialFourier W a b ha hW,
    normalizedRadialFourier_mellin_inversion W a b ha hW σ x hσ hσ1 hx]
  exact (besselZeroTransform_eq_normalizedRadialFourier_of_positive_support
    W a b ha hW hx).symm

/-- The actual `J₀` transform is the inverse Mellin transform of the Gamma
ratio multiplier. Vertical convergence follows from compact source decay. -/
theorem besselZeroTransform_gamma_inversion
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ x : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hx : 0 < x) :
    mellinInv σ (fun s ↦ (Complex.Gamma s / Complex.Gamma (1 - s)) *
      mellin W (1 - s)) x = besselZeroTransform W x := by
  calc
    _ = mellinInv σ (mellin (besselZeroTransform W)) x := by
      unfold mellinInv
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [besselZeroTransform_mellin W a b ha hW _
        (by simpa using hσ) (by simpa using hσ1)]
    _ = _ := besselZeroTransform_mellin_inversion W a b ha hW σ x hσ hσ1 hx

theorem weightOneBesselTransform_eq_besselZeroTransform (H : ℝ → ℂ) (y : ℝ) :
    weightOneBesselTransform H y =
      ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        besselZeroTransform H (4 * Real.pi ^ 2 * y) := by
  unfold weightOneBesselTransform besselZeroTransform
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  congr 2
  rw [show x * (4 * Real.pi ^ 2 * y) = (2 * Real.pi) ^ 2 * (x * y) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.pi)]
  push_cast
  ring

/-- The inverse Mellin representation with the exact `2πi` and `4π²` factors
of the weight-one transform in (5.3). -/
theorem weightOneBesselTransform_gamma_inversion
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (σ y : ℝ)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hy : 0 < y) :
    weightOneBesselTransform W y = ((2 * Real.pi : ℝ) : ℂ) * Complex.I *
      mellinInv σ (fun s ↦ (Complex.Gamma s / Complex.Gamma (1 - s)) *
        mellin W (1 - s)) (4 * Real.pi ^ 2 * y) := by
  rw [besselZeroTransform_gamma_inversion W a b ha hW σ _ hσ hσ1 (by positivity)]
  exact weightOneBesselTransform_eq_besselZeroTransform W y

end ArtinMatthews
