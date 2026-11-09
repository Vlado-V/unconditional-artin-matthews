module

public import ArtinMatthews.SpectralEisensteinFourierCompact
public import ArtinMatthews.SpectralPrimitiveFourierPoincare
public import ArtinMatthews.SpectralStoneEisensteinPair


set_option backward.privateInPublic true
@[expose] public section

/-! The compact Eisenstein amplitude for the primitive parabolic seed.
The raw common-period factor 2N becomes exactly the true width, and
the height change to unit coordinates removes that remaining factor. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem spectralFourierHeightPairing_dilation (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (C : ℝ → ℂ) :
    w • (∫ y in Ioi Y, (ρ y/y^2) • C y) =
      ∫ u in Ioi (Y/w), (ρ (w*u)/u^2) • C (w*u) := by
  have h := integral_comp_mul_left_Ioi' (fun y => (ρ y/y^2) • C y) (Y/w) hw
  rw [mul_div_cancel₀ Y hw.ne'] at h
  rw [← h,smul_smul,← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hu0 : 0 < u := (div_pos hY hw).trans hu
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne',Complex.ofReal_ne_zero.mpr hu0.ne']

theorem spectralFourierHeightPairing_dilation_integrable (w Y : ℝ) (hw : 0 < w) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (C : ℝ → ℂ)
    (hi : IntegrableOn (fun y => (ρ y/y^2) • C y) (Ioi Y)) :
    IntegrableOn (fun u => (ρ (w*u)/u^2) • C (w*u)) (Ioi (Y/w)) := by
  have hComp : IntegrableOn (fun u => (ρ (w*u)/(w*u)^2) • C (w*u)) (Ioi (Y/w)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun y => (ρ y/y^2) • C y) (Y/w) hw).mpr
    simpa only [mul_div_cancel₀ Y hw.ne'] using hi
  apply (hComp.smul (w*w)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := (div_pos hY hw).trans hu
  change (w*w) • ((ρ (w*u)/(w*u)^2) • C (w*u)) = (ρ (w*u)/u^2) • C (w*u)
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_pow]
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne',Complex.ofReal_ne_zero.mpr hu0.ne']

theorem gamma0PrimitiveEisensteinFourier_compact_test (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0CuspEisensteinMeromorphicTest N a
      (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ) s =
        (gamma0CuspTrueWidth N r : ℝ) •
          ∫ y in Ioi Y, (ρ y/y^2) • gamma0CuspEisensteinFourierCoefficient N a r Y hY m s y := by
  rw [gamma0PrimitiveFourierPoincareSeed,gamma0CuspEisensteinMeromorphicTest_smul_seed,
    gamma0PrimitiveFourierScale_conj,
    gamma0CuspEisensteinMeromorphicTest_fourier N a r Y hY m s ρ hρ hcρ hpρ hsρ]
  rw [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_natCast,
    ← mul_assoc,gamma0PrimitiveFourierScale_two_N,Complex.real_smul,Complex.ofReal_natCast]

theorem gamma0PrimitiveEisensteinFourier_unit_test (N : ℕ) [NeZero N]
    (a r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (m : ℤ) (s : ℂ)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hpρ : tsupport ρ ⊆ Ioi (0 : ℝ)) (hsρ : tsupport ρ ⊆ Ioi Y) :
    gamma0CuspEisensteinMeromorphicTest N a
      (gamma0PrimitiveFourierPoincareSeed N r m ρ hρ hcρ hpρ) s =
        ∫ u in Ioi (Y/(gamma0CuspTrueWidth N r : ℝ)),
          (ρ ((gamma0CuspTrueWidth N r : ℝ)*u)/u^2) •
            gamma0CuspEisensteinFourierCoefficient N a r Y hY m s
              ((gamma0CuspTrueWidth N r : ℝ)*u) := by
  rw [gamma0PrimitiveEisensteinFourier_compact_test N a r Y hY m s ρ hρ hcρ hpρ hsρ]
  exact spectralFourierHeightPairing_dilation _ Y
    (Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)) hY ρ _

end ArtinMatthews

