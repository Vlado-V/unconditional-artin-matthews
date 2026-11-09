module

public import ArtinMatthews.SpectralFourierBruhatKernel
public import ArtinMatthews.SpectralPoincareDoubleCosetKernel


set_option backward.privateInPublic true
@[expose] public section

/-! The actual compact Fourier Poincare pairing as a geometric matrix sum,
joined to the native cusp spectral identity with its noncuspidal remainder.
All matrices, including the zero and negative lower-left sectors, remain. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace BigOperators

namespace ArtinMatthews

theorem gamma0FourierPoincareTest_geometric_sum (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (ρ η : ℝ → ℝ)
    (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    inner ℂ (gamma0FourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0FourierPoincareTest N s n η hη hcη hpη) =
      2 * ∑ᶠ M : gamma0CuspCorrespondence N r s,
        compactPoincareGeometricKernel
          (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
          (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M.val :=
  gamma0SmoothSeedMass_pairing_geometric N r s _ _

theorem gamma0FourierPoincareTest_spectral_geometric (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    (2 * ∑ᶠ M : gamma0CuspCorrespondence N r s,
        compactPoincareGeometricKernel
          (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
          (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M.val) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0FourierPoincareSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0FourierPoincareSpectralCoefficient N i s Y hY n hn η)) +
      inner ℂ (gamma0NoncuspidalRemainder N (gamma0FourierPoincareTest N r m ρ hρ hcρ hpρ))
        (gamma0NoncuspidalRemainder N (gamma0FourierPoincareTest N s n η hη hcη hpη)) := by
  rw [← gamma0FourierPoincareTest_geometric_sum N r s m n ρ η hρ hη hcρ hcη hpρ hpη]
  exact gamma0FourierPoincareTest_spectral_pairing N r s Y hY m n hm hn
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

end ArtinMatthews
