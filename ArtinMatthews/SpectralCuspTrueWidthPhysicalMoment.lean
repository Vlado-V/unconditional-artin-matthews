module

public import ArtinMatthews.SpectralCuspTrueWidthBesselScale
public import ArtinMatthews.SpectralFrequencyTestProfile


set_option backward.privateInPublic true
@[expose] public section

/-! Literal finite physical moments in true-width normalization. -/

noncomputable section
open Set MeasureTheory
open OAI.CubicEisenstein
open scoped MatrixGroups ContDiff BigOperators

namespace ArtinMatthews

def gamma0CuspPhysicalBesselMoment (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (a : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℝ) : ℝ :=
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let nN := (gamma0CuspFrequencyStep N a : ℤ)*n
  let T (i : Gamma0AllHeightSpectralIndex N) : ℂ :=
    ∫ x : ℝ, (F x : ℂ)*schlafliBesselK
      (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))) x ∂spectralKLPhysicalMeasure
  ∑ i ∈ u, ‖T i‖^2*‖(Real.sqrt w : ℂ)*gamma0CuspBesselAmplitude N i a Y hY nN
    (gamma0CuspFrequencyStep_mul_ne_zero N a hn)‖^2

theorem gamma0CuspPhysicalBesselMoment_le_scaled_norm (N : ℕ) [NeZero N]
    (u : Finset (Gamma0AllHeightSpectralIndex N)) (a : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (n : ℤ) (hn : n ≠ 0) (F ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y)
    (hProfile : ρ = spectralFrequencyTestProfile
      (|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N a : ℝ)) F) :
    let w := (gamma0CuspTrueWidth N a : ℝ)
    let nN := (gamma0CuspFrequencyStep N a : ℤ)*n
    (2*(N : ℝ))^2*gamma0CuspPhysicalBesselMoment N u a Y hY n hn F ≤
      w*‖gamma0FourierPoincareTest N a nN ρ hρ hcρ hpρ‖^2 := by
  subst ρ
  dsimp only
  let w := (gamma0CuspTrueWidth N a : ℝ)
  let q := |cuspFourierFrequency 1 n|/w
  let ρ := spectralFrequencyTestProfile q F
  have hw : 0 < w := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N a)
  have hq : 0 < q := div_pos (abs_pos.mpr (cuspFourierFrequency_ne_zero 1 one_pos n hn)) hw
  have h := gamma0FourierPoincareTest_trueWidth_finite_bessel N u a Y hY n hn ρ hρ hcρ hpρ hsρ
  dsimp only at h
  have hT (i : Gamma0AllHeightSpectralIndex N) :
      cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
        (|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N a : ℝ)) Y ρ =
      ∫ x : ℝ, (F x : ℂ)*schlafliBesselK
        (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ))) x ∂spectralKLPhysicalMeasure :=
    spectralFrequencyTestProfile_transform q hq F _ Y hY.le hsρ
  unfold gamma0CuspPhysicalBesselMoment
  dsimp only
  simpa only [hT] using h

end ArtinMatthews
