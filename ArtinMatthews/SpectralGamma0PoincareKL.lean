module

public import ArtinMatthews.SpectralKLCuspHeightTransform
public import ArtinMatthews.SpectralGamma0PoincareBessel
public import Mathlib.Analysis.RCLike.Sqrt


set_option backward.privateInPublic true
@[expose] public section

/-! Actual principal-series cuspidal Poincare coefficients use the proved
KL transform. The premise lambda>=1/4 selects this sector explicitly;
the existing arbitrary-order theorem retains the other sectors. -/

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff MatrixGroups ComplexOrder

namespace ArtinMatthews

theorem spectralComplexSqrt_quarter_sub_real (eig : ℝ) (heig : 1/4 ≤ eig) :
    Complex.sqrt (1/4-(eig : ℂ)) = (Real.sqrt (eig-1/4) : ℂ)*Complex.I := by
  have hp : (0 : ℂ) ≤ ((eig-1/4 : ℝ) : ℂ) :=
    RCLike.nonneg_iff_exists_ofReal.mpr ⟨eig-1/4,sub_nonneg.mpr heig,rfl⟩
  rw [show (1/4 : ℂ)-(eig : ℂ) = -((eig-1/4 : ℝ) : ℂ) by push_cast; ring,
    Complex.sqrt_neg_of_nonneg hp,Complex.sqrt_of_nonneg hp,Complex.ofReal_re]
  exact mul_comm _ _

theorem gamma0FourierPoincareTest_native_principal_KL (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N)
    (heig : 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos)
      (gamma0FullCuspidalSpectralBasis N i).val =
        (2*(N : ℂ))*gamma0CuspBesselAmplitude N i r Y hY n hn*
          spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest |cuspFourierFrequency (N : ℝ) n| ρ)
            (Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)) := by
  have hq : 0 < |cuspFourierFrequency (N : ℝ) n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero (N : ℝ) (by exact_mod_cast NeZero.pos N) n hn)
  rw [gamma0FourierPoincareTest_native_inner N i r Y hY n hn ρ hρ hcρ hpos hs,
    spectralComplexSqrt_quarter_sub_real _ heig,
    cuspBesselTransform_imaginary_eq_KL hq hY ρ hρ.continuous hcρ hs]

theorem gamma0FourierPoincareTest_native_principal_projected_KL (N : ℕ) [NeZero N]
    (i : Gamma0AllHeightSpectralIndex N)
    (heig : 1/4 ≤ gamma0AllHeightGradientSpectralValue N i) (r : SL(2, ℤ))
    (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0CuspidalProjection N (gamma0FourierPoincareTest N r n ρ hρ hcρ hpos))
      (gamma0FullCuspidalSpectralBasis N i) =
        (2*(N : ℂ))*gamma0CuspBesselAmplitude N i r Y hY n hn*
          spectralKLPhysicalAnalysisIntegral
            (spectralKLHeightPhysicalTest |cuspFourierFrequency (N : ℝ) n| ρ)
            (Real.sqrt (gamma0AllHeightGradientSpectralValue N i-1/4)) := by
  rw [gamma0CuspidalProjection_inner_right]
  exact gamma0FourierPoincareTest_native_principal_KL N i heig r Y hY n hn ρ hρ hcρ hpos hs

end ArtinMatthews
