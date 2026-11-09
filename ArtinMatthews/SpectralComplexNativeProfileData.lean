module

public import ArtinMatthews.SpectralComplexNativeProfile
public import ArtinMatthews.SpectralABLNativeWindowAction


set_option backward.privateInPublic true
@[expose] public section

/-! A real complex-valued physical profile with the proved envelopes
gives an actual native decaying profile at every true cusp width. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
namespace ArtinMatthews

theorem gamma0NativeComplexProfile_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (n : ℤ) (hn : n ≠ 0) (F : ℝ → ℂ)
    (hF : ContDiffOn ℝ ∞ F (Ioi (0 : ℝ)))
    (hzero : ∀ x : ℝ, x ≤ 0 → F x = 0)
    (hreal : ∀ x : ℝ, 0 < x → star (F x) = F x)
    (C D : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → ‖F x‖ ≤ C*x^(3/4 : ℝ))
    (hlarge : ∀ x : ℝ, 1 ≤ x → ‖F x‖ ≤ D/x^2) :
    ∃ P : SpectralDecayingHeightProfile,
      P.exponent = 5/4 ∧
      (∀ y : ℝ, P.value y = Real.sqrt (y/(gamma0CuspTrueWidth N r : ℝ))*
        (F ((|cuspFourierFrequency 1 n|/(gamma0CuspTrueWidth N r : ℝ))*y)).re) ∧
      gamma0PrimitivePhysicalTest N r n P.value = F := by
  have hq : 0 < |cuspFourierFrequency 1 n| :=
    abs_pos.mpr (cuspFourierFrequency_ne_zero 1 zero_lt_one n hn)
  have hw : 0 < (gamma0CuspTrueWidth N r : ℝ) := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hM : 0 ≤ max C D := hC.trans (le_max_left _ _)
  have hs (x : ℝ) (hx : 0 < x) : ‖F x‖ ≤ max C D*x^(3/4 : ℝ) :=
    (hsmall x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx.le _))
  have hl (x : ℝ) (hx : 1 ≤ x) : ‖F x‖ ≤ max C D/x^2 :=
    (hlarge x hx).trans (div_le_div_of_nonneg_right (le_max_right _ _) (sq_nonneg x))
  obtain ⟨P,hP,hvalue,hphysical⟩ := spectralComplexProfile_native_exists hq hw hM F hF hreal hs hl
  exact ⟨P,hP,hvalue,gamma0PrimitivePhysicalTest_eq N r n hn P.value F hzero hphysical⟩

end ArtinMatthews
