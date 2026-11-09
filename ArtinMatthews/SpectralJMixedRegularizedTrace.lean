module

public import ArtinMatthews.SpectralJNativeHeatSource
public import ArtinMatthews.SpectralJRegularizedSourceAbsolute
public import ArtinMatthews.SpectralMixedJHeatTannery
public import ArtinMatthews.SpectralBareTestDominance
public import ArtinMatthews.SpectralMixedCuspInequivalent


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter Complex
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0MixedJ_regularized_bare_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n)
    (L : ℝ) (hL : 0 ≤ L) :
    gamma0BareSourceSpectralSide (r * s) (spectralJRegularizedEnergyTest f hf hc hp L hL)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm =
      (1 / 4 : ℂ) * ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJRegularizedWeight f L) := by
  obtain ⟨hC, hI⟩ := gamma0JRegularizedSource_absolute_swapped
    f hf hc hp r s hcop Y hY m n hm hn L hL
  have hSpectral := gamma0HeatSourceSpectralSide_tendsto_of_bare (r * s)
    (spectralJRegularizedEnergyTest f hf hc hp L hL)
    (gamma0CuspOneOver s) 1 Y hY n m hn hm hC hI
  have hGeometric := (gamma0MixedJRegularizedHeatSeries_tendsto_bare
    f hf hc hp r s hcop m n hmn L hL).2
  apply tendsto_nhds_unique hSpectral
  apply (tendsto_const_nhds.mul hGeometric).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (gamma0JHeatSource_inequivalent_trace (r * s)
    (gamma0CuspOneOver s) 1 (gamma0MixedCusps_inequivalent_of_one_lt r s hr)
    Y hY n m hn hm (by simpa only [mul_comm n m] using hmn)
    f hf hc hp hreal L R hL hR).symm

end
end ArtinMatthews
