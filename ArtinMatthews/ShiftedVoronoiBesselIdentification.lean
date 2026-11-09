module

public import ArtinMatthews.ShiftedVoronoiBesselRegularity
public import ArtinMatthews.ShiftedVoronoiLaplaceUniqueness
public import ArtinMatthews.ShiftedVoronoiRadialNormalization


set_option backward.privateInPublic true
@[expose] public section

/-!
# Identifying the actual Bessel transform with radial Fourier transform

For a smooth compact source on the positive half-line, both transforms have
the same proved Laplace transform. Half-line uniqueness identifies them.
This transfers the established Schwartz Fourier theory to the actual `J₀`
kernel without assuming a Hankel or Voronoi formula.
-/

noncomputable section
open MeasureTheory Set Complex

namespace ArtinMatthews

theorem besselZeroTransform_eq_normalizedRadialFourier
    (W : SchwartzMap ℝ ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hWs : Function.support W ⊆ Icc 0 B) :
    EqOn (besselZeroTransform W) (normalizedRadialFourier W) (Ioi 0) := by
  have hWk : HasCompactSupport (W : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hWs
  have hHs : ∀ x, B < x → W x = 0 := by
    intro x hx
    by_contra hn
    exact (not_le_of_gt hx) (hWs hn).2
  apply eqOn_Ioi_of_laplace_eq _ _
    (continuous_besselZeroTransform W W.continuous hWk).continuousOn
    (normalizedRadialFourier_continuous W).continuousOn B
  · intro t ht
    simpa only [Complex.ofReal_exp, Complex.ofReal_neg] using
      besselZeroTransform_laplace_integrable W W.continuous W.integrable.integrableOn
        B t hHs ht
  · intro t ht
    exact normalizedRadialFourier_laplace_integrable W t (lt_of_le_of_lt hB ht)
  · intro t ht
    change radialLaplace (besselZeroTransform W) t =
      radialLaplace (normalizedRadialFourier W) t
    rw [normalizedRadialFourier_laplace W t (lt_of_le_of_lt hB ht)]
    have he := besselZeroTransform_laplace W W.continuous W.integrable.integrableOn
      B t hB hHs ht
    simpa only [radialLaplace, Complex.ofReal_exp, Complex.ofReal_neg,
      div_eq_mul_inv, one_mul, mul_one, mul_comm] using he

end ArtinMatthews
