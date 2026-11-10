module

public import ArtinMatthews.ShiftedVoronoiBesselDuality
public import ArtinMatthews.ShiftedVoronoiRadialNormalization
public import ArtinMatthews.ShiftedVoronoiBesselIdentification
public import ArtinMatthews.ShiftedVoronoiNormalizedMellin
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin multiplier of the actual Bessel transform

The identity follows from the proved identification with radial Fourier
transform. Convergence is included and the source may be any smooth compact
test supported away from zero, represented as a Schwartz function.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

theorem besselZeroTransform_eq_normalizedRadialFourier_of_positive_support
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    EqOn (besselZeroTransform W) (normalizedRadialFourier W) (Ioi 0) := by
  apply besselZeroTransform_eq_normalizedRadialFourier W (max b 0) (le_max_right _ _)
  intro x hx
  have hh := hW hx
  exact ⟨ha.le.trans hh.1, hh.2.trans (le_max_left _ _)⟩

theorem mellin_besselZeroTransform_eq_normalizedRadialFourier
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) :
    mellin (besselZeroTransform W) = mellin (normalizedRadialFourier W) := by
  funext s
  unfold mellin
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [besselZeroTransform_eq_normalizedRadialFourier_of_positive_support W a b ha hW hx]

theorem besselZeroTransform_mellinConvergent
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (besselZeroTransform W) s := by
  apply (normalizedRadialFourier_mellinConvergent W s hs).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (x : ℂ) ^ (s - 1) • normalizedRadialFourier W x =
    (x : ℂ) ^ (s - 1) • besselZeroTransform W x
  rw [besselZeroTransform_eq_normalizedRadialFourier_of_positive_support W a b ha hW hx]

theorem besselZeroTransform_mellin
    (W : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0 < a)
    (hW : Function.support W ⊆ Icc a b) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s.re < 1) :
    mellin (besselZeroTransform W) s =
      (Complex.Gamma s / Complex.Gamma (1 - s)) * mellin W (1 - s) := by
  rw [mellin_besselZeroTransform_eq_normalizedRadialFourier W a b ha hW]
  exact normalizedRadialFourier_mellin W a b ha hW s hs hs1

end ArtinMatthews
