module

public import ArtinMatthews.SpectralJMixedBareTrace
public import ArtinMatthews.SpectralJMixedGeometricParts
public import ArtinMatthews.SpectralJMixedSourceLinearity


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Set Complex
open scoped ContDiff MatrixGroups
noncomputable section

theorem gamma0MixedJ_modulus_trace
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hp : tsupport f ⊆ Ioi (0 : ℝ))
    (r s : ℕ) [NeZero r] [NeZero s] (hr : 1 < r) (hcop : r.Coprime s)
    (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) (hmn : 0 < m * n) :
    (∑' q : Ioi (0 : ℕ),
      gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m f) =
      4 * gamma0BareSourceSpectralSide (r * s) (spectralJClippedEnergyTest f hf hc hp)
        (gamma0CuspOneOver s) 1 Y hY n m hn hm +
      (∑' q : Ioi (0 : ℕ),
        gamma0ABLOppositeGeometricTerm (r * s) (gamma0CuspOneOver s) 1 q n m
          (spectralJOddSynthesis f)) := by
  have hR := gamma0MixedJ_modulus_trace_real (spectralJRealTest f)
    (spectralJRealTest_contDiff f hf) (spectralJRealTest_hasCompactSupport f hc)
    ((spectralJRealTest_tsupport f).trans hp) (spectralJRealTest_conj f)
    r s hr hcop Y hY m n hm hn hmn
  have hI := gamma0MixedJ_modulus_trace_real (spectralJImagTest f)
    (spectralJImagTest_contDiff f hf) (spectralJImagTest_hasCompactSupport f hc)
    ((spectralJImagTest_tsupport f).trans hp) (spectralJImagTest_conj f)
    r s hr hcop Y hY m n hm hn hmn
  have hsource := gamma0MixedJ_clipped_source_parts f hf hc hp r s hcop Y hY m n hm hn
  have hgeom := gamma0MixedJ_geometric_parts f hf hc hp r s hcop m n hm hn hmn
  rw [hgeom.1, hR, hI, hsource, hgeom.2]
  ring

end
end ArtinMatthews
