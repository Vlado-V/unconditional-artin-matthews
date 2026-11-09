module

public import ArtinMatthews.SpectralMixedCuspPhysicalBessel
public import ArtinMatthews.SpectralCuspExceptionalMoment


set_option backward.privateInPublic true
@[expose] public section

/-! The finite exceptional-series singleton at the actual source cusp 1/s. -/

noncomputable section
open scoped MatrixGroups

namespace ArtinMatthews

theorem gamma0MixedCusp_exceptional_singleton_compact_bound (r s : ℕ) [NeZero r] [NeZero s]
    (hcop : r.Coprime s) (u : Finset (Gamma0AllHeightSpectralIndex (r*s)))
    (n : ℤ) (hn : n ≠ 0) {A Y : ℝ} (hA : 0 < A) (hA₁ : 2*A ≤ 1) (hY : 0 < Y)
    (hYA : Y < A/(|cuspFourierFrequency 1 n|/
      (gamma0CuspTrueWidth (r*s) (gamma0CuspOneOver s) : ℝ)))
    (heig : ∀ i ∈ u, gamma0AllHeightGradientSpectralValue (r*s) i ≤ 1/4) :
    (Real.exp (-Real.exp 1)/16)^2*gamma0CuspExceptionalMoment (r*s) u (gamma0CuspOneOver s) Y hY n hn A ≤
      1+8*spectralKloostermanDiagSum (r*s) n (|cuspFourierFrequency 1 n|/A) := by
  obtain ⟨F,hF,hcF,hSF,h01,hOne⟩ := spectralKExceptionalPhysicalTest_exists hA
  exact (gamma0CuspExceptionalMoment_le_physical (r*s) u (gamma0CuspOneOver s) Y hY n hn F
    hF.continuous hA hA₁ hSF (fun x => (h01 x).1) hOne heig).trans
      (gamma0MixedSameCusp_comparable_physical_finite_bessel r s hcop u n hn F hF hcF hA hY hYA hSF h01)

end ArtinMatthews
