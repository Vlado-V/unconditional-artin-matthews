module

public import ArtinMatthews.SpectralTrueWidthOrbitalBessel
public import ArtinMatthews.SpectralPositiveModulusReindex


set_option backward.privateInPublic true
@[expose] public section

/-! Exact positive-modulus Bessel rewriting of the genuine Poincare
pairing.  The grouped arithmetic sum has finite support.  The zero
modulus, full native cuspidal sum, and the actual noncuspidal remainder
are retained with their literal coefficients. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0TrueWidthPositiveBesselFibre (N : ℕ) [NeZero N] (r s : SL(2, ℤ))
    (c : Ioi (0 : ℕ)) (m n : ℤ) (ρ η : ℝ → ℝ) : ℂ :=
  letI : NeZero c.val := ⟨(show 0 < c.val from c.property).ne'⟩
  gamma0TrueWidthBesselGeometricFibre N r s c.val m n ρ η

theorem gamma0PositiveGeometricSum_trueWidth_bessel (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ)) :
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη
    Function.HasFiniteSupport (fun c : Ioi (0 : ℕ) => gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η) ∧
      gamma0PositiveGeometricSum N r s ψ φ =
        ∑ᶠ c : Ioi (0 : ℕ), gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η := by
  dsimp only
  let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ
  let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
    ((gamma0CuspFrequencyStep N s : ℤ)*n) η hη hcη hpη
  have he : (fun c : Ioi (0 : ℕ) => ∑ᶠ M : gamma0CuspMatrixFibre N r s c.val,
      compactPoincareGeometricKernel ψ φ M.val) =
      fun c : Ioi (0 : ℕ) => gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η := by
    funext c
    let _ : NeZero c.val := ⟨(show 0 < c.val from c.property).ne'⟩
    exact gamma0PositiveGeometricFibre_trueWidth_bessel N r s c.val m n hm hn ρ η hρ hη hcρ hcη hpρ hpη
  exact he ▸ gamma0PositiveGeometricSum_modulus_fibres N r s ψ φ

theorem gamma0CuspFrequencyStep_mul_ne_zero (N : ℕ) [NeZero N] (r : SL(2, ℤ))
    {m : ℤ} (hm : m ≠ 0) : (gamma0CuspFrequencyStep N r : ℤ)*m ≠ 0 :=
  mul_ne_zero (by exact_mod_cast (gamma0CuspFrequencyStep_pos N r).ne') hm

theorem gamma0FourierPoincareTest_trueWidth_bessel_pairing (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (ρ η : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hη : ContDiff ℝ ∞ η)
    (hcρ : HasCompactSupport ρ) (hcη : HasCompactSupport η)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hpη : tsupport η ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) (hsη : tsupport η ⊆ Ioi Y) :
    let mN := (gamma0CuspFrequencyStep N r : ℤ)*m
    let nN := (gamma0CuspFrequencyStep N s : ℤ)*n
    let ψ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) mN ρ hρ hcρ hpρ
    let φ := cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N)) nN η hη hcη hpη
    let P := gamma0FourierPoincareTest N r mN ρ hρ hcρ hpρ
    let Q := gamma0FourierPoincareTest N s nN η hη hcη hpη
    2*gamma0ZeroGeometricSum N r s ψ φ +
      4*(∑ᶠ c : Ioi (0 : ℕ), gamma0TrueWidthPositiveBesselFibre N r s c m n ρ η) =
      (∑' i : Gamma0AllHeightSpectralIndex N,
        gamma0FourierPoincareSpectralCoefficient N i r Y hY mN (gamma0CuspFrequencyStep_mul_ne_zero N r hm) ρ*
          star (gamma0FourierPoincareSpectralCoefficient N i s Y hY nN (gamma0CuspFrequencyStep_mul_ne_zero N s hn) η)) +
        inner ℂ (gamma0NoncuspidalRemainder N P) (gamma0NoncuspidalRemainder N Q) := by
  dsimp only
  rw [← (gamma0PositiveGeometricSum_trueWidth_bessel N r s m n hm hn ρ η hρ hη hcρ hcη hpρ hpη).2]
  exact gamma0FourierPoincareTest_orbital_spectral N r s Y hY _ _
    (gamma0CuspFrequencyStep_mul_ne_zero N r hm) (gamma0CuspFrequencyStep_mul_ne_zero N s hn)
    ρ η hρ hη hcρ hcη hpρ hpη hsρ hsη

end ArtinMatthews
