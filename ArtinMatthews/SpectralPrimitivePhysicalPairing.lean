module

public import ArtinMatthews.SpectralTrueWidthPhysicalCompact


set_option backward.privateInPublic true
@[expose] public section

/-! The native compact Poincare pairing expressed with the actual
physical fibres, including the full zero-modulus sector. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitiveFourierPoincareTest_physical (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareTest N s n η hη hcη hpη) =
      (gamma0PrimitiveFourierScale N r*gamma0PrimitiveFourierScale N s)*
        (2*gamma0ZeroGeometricSum N r s ψ φ) +
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r s c m n
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
          (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y)))
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
          (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) := by
  dsimp only
  rw [gamma0PrimitiveFourierPoincareTest_geometric N r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη]
  congr 1
  rw [← tsum_eq_finsum (L := SummationFilter.unconditional (Ioi (0 : ℕ)))
    (gamma0PrimitivePositiveBesselFibre_finite N r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη)]
  exact tsum_congr (fun c => gamma0PrimitivePositiveBesselFibre_eq_physical N r s c m n hm hn
    ρ η hρ.continuous hη.continuous hcρ hcη hpρ hpη)

theorem gamma0PrimitiveFourierPoincareTest_sameCusp_physical (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
      (gamma0PrimitiveFourierPoincareTest N r n η hη hcη hpη) =
      (if m = n then (gamma0CuspTrueWidth N r : ℂ)*(cuspFourierHeightPairing ρ η : ℂ) else 0) +
      ∑' c : Ioi (0 : ℕ), gamma0TrueWidthPhysicalFibre N r r c m n
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 n|
          (fun y => η ((gamma0CuspTrueWidth N r : ℝ)*y)))
        (spectralKLHeightPhysicalTest |cuspFourierFrequency 1 m|
          (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))) := by
  rw [gamma0PrimitiveFourierPoincareTest_physical N r r m n hm hn ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0PrimitiveFourier_zero_sameCusp N r m n ρ η hρ hη hcρ hcη hpρ hpη]

end ArtinMatthews
