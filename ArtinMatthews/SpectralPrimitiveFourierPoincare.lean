module

public import ArtinMatthews.SpectralTrueWidthBesselPairing
public import ArtinMatthews.SpectralKLCuspWidthTransform


set_option backward.privateInPublic true
@[expose] public section

/-! The primitive parabolic Fourier Poincare seed. Its literal factor
w/(2N) removes the proved central multiplicity and the common-period
index. The cusp coefficient has the exact square-root width factor. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

def gamma0PrimitiveFourierScale (N : ℕ) [NeZero N] (r : SL(2, ℤ)) : ℂ :=
  ((gamma0CuspTrueWidth N r : ℝ)/(2*(N : ℝ)) : ℝ)

theorem gamma0PrimitiveFourierScale_conj (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    (starRingEnd ℂ) (gamma0PrimitiveFourierScale N r) = gamma0PrimitiveFourierScale N r :=
  Complex.conj_ofReal _

theorem gamma0PrimitiveFourierScale_two_N (N : ℕ) [NeZero N] (r : SL(2, ℤ)) :
    gamma0PrimitiveFourierScale N r * (2*(N : ℂ)) = (gamma0CuspTrueWidth N r : ℂ) := by
  unfold gamma0PrimitiveFourierScale
  push_cast
  field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]

theorem gamma0PrimitiveFourierScale_indices (N : ℕ) [NeZero N] (r s : SL(2, ℤ)) :
    gamma0PrimitiveFourierScale N r * gamma0PrimitiveFourierScale N s *
      (4*((gamma0CuspFrequencyStep N s : ℂ)*(gamma0CuspFrequencyStep N r : ℂ))) = 1 := by
  have hr : (gamma0CuspTrueWidth N r : ℂ)*(gamma0CuspFrequencyStep N r : ℂ) = (N : ℂ) := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N r
  have hs : (gamma0CuspTrueWidth N s : ℂ)*(gamma0CuspFrequencyStep N s : ℂ) = (N : ℂ) := by
    exact_mod_cast gamma0CuspFrequencyStep_mul_width N s
  unfold gamma0PrimitiveFourierScale
  push_cast
  field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast NeZero.ne N]
  calc
    _ = ((gamma0CuspTrueWidth N r : ℂ)*(gamma0CuspFrequencyStep N r : ℂ))*
        ((gamma0CuspTrueWidth N s : ℂ)*(gamma0CuspFrequencyStep N s : ℂ))*4 := by ring
    _ = _ := by rw [hr,hs];ring

def gamma0PrimitiveFourierPoincareSeed (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (m : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) : h2SmoothCompactSeeds :=
  gamma0PrimitiveFourierScale N r • modularTranslateSmoothSeed r
    (cuspFourierTestSeed (N : ℝ) (Nat.cast_pos.mpr (NeZero.pos N))
      ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ)

def gamma0PrimitiveFourierPoincareTest (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (m : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) : Gamma0RegionL2 N :=
  gamma0SmoothSeedMass N (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ)

theorem gamma0PrimitiveFourierPoincareTest_eq (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (m : ℤ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ =
      gamma0PrimitiveFourierScale N r • gamma0FourierPoincareTest N r
        ((gamma0CuspFrequencyStep N r : ℤ)*m) ρ hρ hcρ hpρ := by
  exact (gamma0SmoothSeedMass N).map_smul _ _

def gamma0PrimitiveFourierSpectralCoefficient (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m : ℤ) (hm : m ≠ 0) (ρ : ℝ → ℝ) : ℂ :=
  (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) *
    gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
      (gamma0CuspFrequencyStep_mul_ne_zero N r hm) *
    cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
      |cuspFourierFrequency 1 m| (Y/(gamma0CuspTrueWidth N r : ℝ))
      (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u))

theorem gamma0PrimitiveFourierSpectralCoefficient_eq_scaled (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m : ℤ) (hm : m ≠ 0) (ρ : ℝ → ℝ) :
    gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ =
      gamma0PrimitiveFourierScale N r *
        gamma0FourierPoincareSpectralCoefficient N i r Y hY
          ((gamma0CuspFrequencyStep N r : ℤ)*m) (gamma0CuspFrequencyStep_mul_ne_zero N r hm) ρ := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hsq : (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)^2 = (gamma0CuspTrueWidth N r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hw.le
  have hq : (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  have hCancel : (gamma0CuspTrueWidth N r : ℂ) *
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) := by
    rw [← hsq,pow_two,mul_assoc,mul_inv_cancel₀ hq,mul_one]
  rw [gamma0FourierPoincareSpectralCoefficient,cuspBesselTransform_trueWidth N r _ m Y hY ρ]
  unfold gamma0PrimitiveFourierSpectralCoefficient
  calc
    _ = ((gamma0CuspTrueWidth N r : ℂ) *
        (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹) *
        gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
          (gamma0CuspFrequencyStep_mul_ne_zero N r hm) *
        cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
          |cuspFourierFrequency 1 m| (Y/(gamma0CuspTrueWidth N r : ℝ))
          (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u)) := by rw [hCancel]
    _ = (gamma0PrimitiveFourierScale N r * (2*(N : ℂ))) *
        gamma0CuspBesselAmplitude N i r Y hY ((gamma0CuspFrequencyStep N r : ℤ)*m)
          (gamma0CuspFrequencyStep_mul_ne_zero N r hm) *
        ((Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹ *
          cuspBesselTransform (Complex.sqrt (1/4-(gamma0AllHeightGradientSpectralValue N i : ℂ)))
            |cuspFourierFrequency 1 m| (Y/(gamma0CuspTrueWidth N r : ℝ))
            (fun u => ρ ((gamma0CuspTrueWidth N r : ℝ)*u))) := by
      rw [gamma0PrimitiveFourierScale_two_N]
      ring
    _ = _ := by ring

theorem gamma0PrimitiveFourierSpectralCoefficient_eq_inner (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N) (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (m : ℤ) (hm : m ≠ 0) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hcρ : HasCompactSupport ρ) (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ))
    (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0PrimitiveFourierSpectralCoefficient N i r Y hY m hm ρ =
      inner ℂ (gamma0PrimitiveFourierPoincareTest N r m ρ hρ hcρ hpρ)
        (gamma0FullCuspidalSpectralBasis N i).val := by
  rw [gamma0PrimitiveFourierPoincareTest_eq,inner_smul_left,
    gamma0PrimitiveFourierScale_conj,← gamma0FourierPoincareSpectralCoefficient_eq_inner N i r Y hY
      _ (gamma0CuspFrequencyStep_mul_ne_zero N r hm) ρ hρ hcρ hpρ hsρ]
  exact gamma0PrimitiveFourierSpectralCoefficient_eq_scaled N i r Y hY m hm ρ

end ArtinMatthews

