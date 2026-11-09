module

public import ArtinMatthews.SpectralAmbientBesselAmplitude
public import ArtinMatthews.SpectralPrimitiveFourierPoincare


set_option backward.privateInPublic true
@[expose] public section

/-! The primitive compact-test coefficient for every genuine ambient
eigenvector, in literal unit-width coordinates. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace
namespace ArtinMatthews

theorem gamma0PrimitiveFourierPoincareTest_ambient_inner (N : ℕ) [NeZero N]
    (eig : ℝ) (heig : 0 ≤ eig) (v : Gamma0RegionL2 N)
    (hG : gamma0Green N v = (((eig+1)⁻¹ : ℝ) : ℂ) • v)
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    inner ℂ (gamma0PrimitiveFourierPoincareTest N r n ρ hρ hcρ hpρ) v =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)*
        gamma0AmbientBesselAmplitude N eig heig v hG r
          ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)*
        cuspBesselTransform (Complex.sqrt (1/4-(eig : ℂ))) |cuspFourierFrequency 1 n|
          (Y/(gamma0CuspTrueWidth N r : ℝ)) (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) := by
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hs : (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)^2 = (gamma0CuspTrueWidth N r : ℂ) := by
    exact_mod_cast Real.sq_sqrt hw.le
  have hsn : (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hw).ne'
  rw [gamma0PrimitiveFourierPoincareTest_eq,inner_smul_left,gamma0PrimitiveFourierScale_conj,
    gamma0FourierPoincareTest_ambient_inner N eig heig v hG r
      ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)
      Y hY ρ hρ hcρ hpρ hsρ,
    cuspBesselTransform_trueWidth N r _ n Y hY ρ]
  have he : (gamma0CuspTrueWidth N r : ℂ)*(Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹ =
      (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ) := by
    rw [← hs,pow_two,mul_assoc,mul_inv_cancel₀ hsn,mul_one]
  calc
    _ = ((gamma0PrimitiveFourierScale N r*(2*(N : ℂ)))*
          (Real.sqrt (gamma0CuspTrueWidth N r : ℝ) : ℂ)⁻¹)*
        gamma0AmbientBesselAmplitude N eig heig v hG r
          ((gamma0CuspFrequencyStep N r : ℤ)*n) (gamma0CuspFrequencyStep_mul_ne_zero N r hn)*
        cuspBesselTransform (Complex.sqrt (1/4-(eig : ℂ))) |cuspFourierFrequency 1 n|
          (Y/(gamma0CuspTrueWidth N r : ℝ)) (fun y => ρ ((gamma0CuspTrueWidth N r : ℝ)*y)) := by ring
    _ = _ := by rw [gamma0PrimitiveFourierScale_two_N,he]

end ArtinMatthews
