module

public import ArtinMatthews.SpectralJRegularizedReality
public import ArtinMatthews.SpectralKLHeatProfiles


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews

open Set Complex
open scoped ContDiff ComplexConjugate
noncomputable section

theorem spectralJRegularizedHeatProfile_properties (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) :
    SpectralKLHeatRegularity (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R) := by
  obtain ⟨C, hC, hb⟩ := spectralJRegularizedWeight_strip_bound f hf hc hp L hL
  exact spectralKLWeightedHeatProfile_properties _ R hR
    (spectralJRegularizedWeight_even f L)
    (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hp L)
    (fun z hz => spectralJRegularizedWeight_differentiableAt f hf.continuous hc hp L z
      (lt_of_le_of_lt hz (by norm_num))) C hC hb

theorem spectralJRegularizedHeatProfile_continued_transform (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (L R : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (ν : ℂ) (hν : |ν.re| ≤ 1 / 2) :
    spectralKLCompactOrderTransform (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R) ν =
      spectralJRegularizedWeight f L (-I * ν) * Complex.exp (ν ^ 2 / (R : ℂ) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := spectralJRegularizedWeight_strip_bound f hf hc hp L hL
  exact spectralKLWeightedHeatProfile_continued_transform _ R hR
    (spectralJRegularizedWeight_even f L)
    (spectralJRegularizedWeight_real_contDiff f hf.continuous hc hp L)
    (fun z hz => spectralJRegularizedWeight_differentiableAt f hf.continuous hc hp L z
      (lt_of_le_of_lt hz (by norm_num))) C hC hb ν hν

theorem spectralJRegularizedHeatProfile_real (f : ℝ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (hReal : ∀ x : ℝ, conj (f x) = f x) (L R x : ℝ) :
    star (spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R x) =
      spectralKLWeightedHeatProfile (spectralJRegularizedWeight f L) R x := by
  apply spectralKLWeightedHeatProfile_real
  intro t
  change conj (spectralJRegularizedWeight f L (t : ℂ)) = _
  rw [spectralJRegularizedWeight_conj f hf hc hp hReal L, Complex.conj_ofReal]

end
end ArtinMatthews
