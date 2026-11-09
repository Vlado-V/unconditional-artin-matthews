module

public import ArtinMatthews.SpectralCuspWidthMultiplicity
public import ArtinMatthews.SpectralTrueWidthKloosterman
public import ArtinMatthews.SpectralTrueWidthOrbitalScaling
public import ArtinMatthews.SpectralOrbitalKloosterman


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine positive-c orbital fibre in primitive cusp coordinates.
The raw Poincare tests retain their exact width-index multiplicity.  The
previous full identity keeps its c=0 term, central signs, and noncuspidal remainder. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0PositiveGeometricFibre_trueWidth (N : ℕ) [NeZero N]
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
          cuspWeylOrbitalKernel 1 m n
            (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y))
            (fun y => η ((gamma0CuspTrueWidth N s : ℝ)*y))
            (gamma0TrueWidthModulus N r s c)
            (gamma0TrueWidthModulus_ne_zero N r s (by exact_mod_cast NeZero.ne c))) := by
  rw [gamma0PositiveGeometricFibre_eq_kloosterman N r s c
    ((gamma0CuspFrequencyStep N r : ℤ)*m) ((gamma0CuspFrequencyStep N s : ℤ)*n)
    ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0PeriodKloostermanSum_trueWidth,cuspWeylOrbitalKernel_trueWidth]
  ring

theorem gamma0PositiveGeometricFibre_eq_zero_of_inadmissible (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (c : ℕ) [NeZero c] (m n : ℤ)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (h : ¬ (gamma0CuspFrequencyStep N r : ℤ) ∣ m ∨
      ¬ (gamma0CuspFrequencyStep N s : ℤ) ∣ n) :
    (∑ᶠ M : gamma0CuspMatrixFibre N r s c, compactPoincareGeometricKernel
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) m ρ hρ hcρ hpρ)
      (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) n η hη hcη hpη) M.val) = 0 := by
  rw [gamma0PositiveGeometricFibre_eq_kloosterman N r s c m n ρ η hρ hη hcρ hcη hpρ hpη,
    gamma0PeriodKloostermanSum_eq_zero_of_inadmissible N r s c m n h,zero_mul]

end ArtinMatthews
