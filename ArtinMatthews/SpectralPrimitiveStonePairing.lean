module

public import ArtinMatthews.SpectralPrimitiveOrbitalPairing
public import ArtinMatthews.SpectralStoneNativePairing


set_option backward.privateInPublic true
@[expose] public section

/-! Full compact primitive-cusp spectral identity. The positive modulus
term has one true-width Kloosterman sum per orbital. Eisenstein and
residual terms remain the actual native spectral contributions. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0PrimitiveFourierPoincareTest_stone (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0PrimitiveFourierSpectralCoefficient N i s Y hY n hn η)) +
      (gamma0StoneEisensteinPair N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) +
        gamma0StoneResidualPair N (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη)) := by
  rw [gamma0PrimitiveFourierPoincareTest,gamma0PrimitiveFourierPoincareTest,
    gamma0CompactStoneNativePairing]
  congr 1
  apply tsum_congr
  intro i
  change inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0FullCuspidalSpectralBasis N i).val *
    inner ℂ (gamma0FullCuspidalSpectralBasis N i).val
      (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη) = _
  rw [← gamma0PrimitiveFourierSpectralCoefficient_eq_inner N i r Y hY m hm ρ hρ hcρ hpρ hsρ]
  congr 1
  rw [gamma0PrimitiveFourierSpectralCoefficient_eq_inner N i s Y hY n hn η hη hcη hpη hsη]
  exact (inner_conj_symm _ _).symm

theorem gamma0PrimitiveFourierPoincareTest_trace (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let nN := (gamma0CuspFrequencyStep N s : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    (gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s) *
        (2*gamma0ZeroGeometricSum N r s ψ φ) +
      (∑ᶠ c : Ioi (0 : ℕ), gamma0PrimitivePositiveBesselFibre N r s c m n ρ η) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0PrimitiveFourierSpectralCoefficient N i s Y hY n hn η)) +
      (gamma0StoneEisensteinPair N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareSeed N s n η hη hcη hpη) +
        gamma0StoneResidualPair N (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη)) := by
  dsimp only
  rw [← gamma0PrimitiveFourierPoincareTest_geometric N r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη]
  exact gamma0PrimitiveFourierPoincareTest_stone N r s Y hY m n hm hn ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

theorem gamma0PrimitiveFourierPoincareTest_sameCusp_trace (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    (if m = n then (gamma0CuspTrueWidth N r : ℂ)*(cuspFourierHeightPairing ρ η : ℂ) else 0) +
      (∑ᶠ c : Ioi (0 : ℕ), gamma0PrimitivePositiveBesselFibre N r r c m n ρ η) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ *
          star (gamma0PrimitiveFourierSpectralCoefficient N i r Y hY n hn η)) +
      (gamma0StoneEisensteinPair N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareSeed N r n η hη hcη hpη) +
        gamma0StoneResidualPair N (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
          (gamma0PrimitiveFourierPoincareTest N r n η hη hcη hpη)) := by
  have h := gamma0PrimitiveFourierPoincareTest_trace N r r Y hY m n hm hn ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη
  dsimp only at h
  rwa [gamma0PrimitiveFourier_zero_sameCusp N r m n ρ η hρ hη hcρ hcη hpρ hpη] at h

end ArtinMatthews

