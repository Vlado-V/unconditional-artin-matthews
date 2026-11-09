module

public import ArtinMatthews.SpectralCuspConstantTermWeakDerivative


set_option backward.privateInPublic true
@[expose] public section

/-! Exact compact testing of the actual globally glued constant terms,
through their bounded genuine positive-height operators. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0GlobalCuspConstantTerm_compact_test (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (Y : ℝ) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi Y) :
    (∫ y in Ioi (0 : ℝ), κ y • gamma0GlobalCuspConstantTerm N r f y) =
      cuspVerticalCompactTest (Nat.cast_pos.mpr (NeZero.pos N)) hY κ hκ hκc
        (gamma0CuspConstantTerm N r Y hY f) := by
  rw [cuspVerticalCompactTest_apply,
    spectralTest_setIntegral_eq_integral κ (Ioi (0 : ℝ))
      (fun _ hy => hY.trans (hκs hy)),
    ← spectralTest_setIntegral_eq_integral κ (Ioi Y) hκs]
  have he := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r f Y hY)
  apply integral_congr_ae
  exact he.mono fun y hy => by dsimp only; rw [hy]

theorem gamma0GlobalCuspConstantTerm_test_integrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N)
    (κ : ℝ → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun y => κ y • gamma0GlobalCuspConstantTerm N r f y) volume :=
  SpectralCuspWeakRegularity.integrable_positive_test_smul
    (gamma0GlobalCuspConstantTerm_locallyIntegrable N r f) hκ hκc hκs

theorem gamma0GlobalCuspConstantTermDerivative_compact_test (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) (Y : ℝ) (hY : 0 < Y)
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ ∞ κ) (hκc : HasCompactSupport κ)
    (hκs : tsupport κ ⊆ Ioi Y) :
    (∫ y in Ioi (0 : ℝ), κ y • gamma0GlobalCuspConstantTermDerivative N r u y) =
      cuspVerticalCompactTest (Nat.cast_pos.mpr (NeZero.pos N)) hY
        (fun y => κ y / y)
        (by simpa only [pow_one] using
          (spectralPositiveTest_div_pow_contDiff κ hκ
            (fun _ hy => hY.trans (hκs hy)) 1).continuous)
        (by simpa only [pow_one] using spectralPositiveTest_div_pow_compact κ hκc 1)
        (gamma0CuspVerticalConstantTerm N r Y hY u) := by
  rw [cuspVerticalCompactTest_apply,
    spectralTest_setIntegral_eq_integral κ (Ioi (0 : ℝ))
      (fun _ hy => hY.trans (hκs hy)),
    ← spectralTest_setIntegral_eq_integral κ (Ioi Y) hκs]
  have he := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTermDerivative_ae N r u Y hY)
  apply integral_congr_ae
  filter_upwards [he] with y hy
  rw [hy]
  simp only [gamma0CuspConstantTermDerivative, div_eq_mul_inv, mul_smul]

end ArtinMatthews
