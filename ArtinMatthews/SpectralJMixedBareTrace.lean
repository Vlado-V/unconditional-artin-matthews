module

public import ArtinMatthews.SpectralJMixedRegularizedTrace
public import ArtinMatthews.SpectralJNativeOrientation
public import ArtinMatthews.SpectralMixedJRegularizationTannery
public import ArtinMatthews.SpectralJMixedGeometric


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open MeasureTheory Set Filter Complex
open scoped ContDiff MatrixGroups Topology ComplexConjugate
noncomputable section

theorem gamma0MixedJ_bare_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
      (gamma0CuspOneOver s) 1 Y hY n m hn hm =
      (1 / 4 : ℂ) * ∑' q : Ioi (0 : ℕ),
        gamma0TrueWidthBareFibre (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJForwardSpectralWeight f) := by
  have hSpectral := gamma0JSource_regularization_tendsto_swapped
    f hf hc hp hreal r s hcop Y hY m n hm hn
  have hGeometric := (gamma0MixedJRegularizedBareSeries_tendsto
    f hf hc hp r s hcop m n hmn).2.comp tendsto_natCast_atTop_atTop
  apply tendsto_nhds_unique hSpectral
  apply (tendsto_const_nhds.mul hGeometric).congr'
  exact Eventually.of_forall (fun k : ℕ =>
    (gamma0MixedJ_regularized_bare_trace_real f hf hc hp hreal r s hr hcop
      Y hY m n hm hn hmn (k : ℝ) (Nat.cast_nonneg k)).symm)

theorem gamma0MixedJ_modulus_trace_real
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ)) (hreal : ∀ x : ℝ, conj (f x) = f x)
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      4 * gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm +
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f)) := by
  have htrace := gamma0MixedJ_bare_trace_real f hf hc hp hreal
    r s hr hcop Y hY m n hm hn hmn
  have hgeom := (gamma0MixedJ_geometric_reconstruction f hf hc hp r s hcop
    m n hm hn hmn).2.2
  rw [hgeom, htrace]
  ring

end
end ArtinMatthews
