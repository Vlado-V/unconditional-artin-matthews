module

public import ArtinMatthews.SpectralWeylTwoHeightKernel
public import ArtinMatthews.SpectralBesselCosineEvaluation
public import ArtinMatthews.SpectralBesselCoshEvaluation


set_option backward.privateInPublic true
@[expose] public section

/-! Actual compact orbital tests have the evaluated two-height cosine kernel.
Primitive cusp widths and all raw Poincare multiplicities remain literal. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem cuspWeylOrbitalKernel_twoHeight_compact (N : ℕ) [NeZero N] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (c : ℤ) (hc : c ≠ 0) :
    cuspWeylOrbitalKernel N m n ρ η c (by exact_mod_cast hc) =
      ∫ y in Ioi (0 : ℝ), ∫ v in Ioo 0 (1/((c : ℝ)^2*y)),
        weylTwoHeightDensity N m n ρ η c y v :=
  cuspWeylOrbitalKernel_twoHeight N m n ρ η c (by exact_mod_cast hc)
    (weylPlanarDensity_integrable N m n ρ η hρ hη hcρ hcη hpρ hpη c hc)

theorem gamma0PositiveGeometricFibre_twoHeight (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
        ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη) M.val) =
      ((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ)) *
        (gamma0TrueWidthKloostermanSum N r s c m n *
          ∫ y in Ioi (0 : ℝ), ∫ v in Ioo 0 (1/((gamma0TrueWidthModulus N r s c)^2*y)),
            weylTwoHeightDensity 1 m n
              (fun t => ρ ((gamma0CuspTrueWidth N r : ℝ)*t))
              (fun t => η ((gamma0CuspTrueWidth N s : ℝ)*t))
              (gamma0TrueWidthModulus N r s c) y v) := by
  rw [gamma0PositiveGeometricFibre_trueWidth N r s c m n ρ η hρ hη hcρ hcη hpρ hpη]
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne c
  have hI := cuspWeylOrbitalIntegrand_trueWidth_integrable N r s m n ρ η
    hρ hη hcρ hcη hpρ hpη (c : ℤ) (by exact_mod_cast NeZero.ne c)
  have hp := weylPlanarDensity_integrable_of_orbital 1 m n
    (fun t => ρ ((gamma0CuspTrueWidth N r : ℝ)*t))
    (fun t => η ((gamma0CuspTrueWidth N s : ℝ)*t))
    (gamma0TrueWidthModulus N r s c) (gamma0TrueWidthModulus_ne_zero N r s hcR) hI
  rw [cuspWeylOrbitalKernel_twoHeight 1 m n _ _ _ _ hp]

end ArtinMatthews
