module

public import ArtinMatthews.SpectralCuspGreenSeparableTest
public import ArtinMatthews.SpectralCuspSeparablePairing
public import ArtinMatthews.SpectralCuspConstantTermGlobalTesting
public import ArtinMatthews.SpectralCuspConstantTermEuler


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient Green operator preserves the genuine all-positive-
height cuspidal mass kernel. Compact period-window tests give the literal
constant-term Euler equation; genuine first weak derivatives, classical
regularity and the proved near-zero/tail energies force its solution to
vanish. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0Green_cusp_second_weak_equation_at_height (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) (hs : tsupport ρ ⊆ Ioi Y)
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0CuspConstantTerm N r Y hY (gamma0Green N f) y) =
      ∫ y in Ioi Y, (ρ y / y ^ 2) • gamma0CuspConstantTerm N r Y hY (gamma0Green N f) y := by
  have he := gamma0Green_twoCell_separable_weak_laplacian N r Y hY ρ hρ hρc hρpos hs f
  dsimp only at he
  rw [gamma0CuspTwoCellMassRestriction_test_pairing,
    gamma0CuspTwoCellMassRestriction_laplacian_pairing,
    gamma0CuspTwoCellMassRestriction_test_pairing] at he
  have hc : gamma0CuspConstantTerm N r Y hY f = 0 :=
    (mem_gamma0AllHeightCuspidalMassSpace_iff_constantTerm N f).mp hf r Y hY
  have hz : (∫ y in Ioi Y, (ρ y / y ^ 2) • gamma0CuspConstantTerm N r Y hY f y) = 0 := by
    rw [hc]
    apply integral_eq_zero_of_ae
    have hzero := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
      (Lp.coeFn_zero ℂ 2 ((cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y))
    filter_upwards [hzero] with y hy
    change (ρ y / y ^ 2) • (0 : CuspVerticalL2 (N : ℝ) Y) y = (0 : ℂ)
    simp only [hy, Pi.zero_apply, smul_zero]
  rw [hz, smul_zero] at he
  have hm := eq_of_sub_eq_zero (show
    (N : ℝ) • (∫ y in Ioi Y, (ρ y / y ^ 2) • gamma0CuspConstantTerm N r Y hY (gamma0Green N f) y) -
      (N : ℝ) • (∫ y in Ioi Y, deriv (deriv ρ) y • gamma0CuspConstantTerm N r Y hY (gamma0Green N f) y) = 0 by
        simpa only [sub_eq_add_neg] using he)
  simp only [Complex.real_smul] at hm
  exact (mul_left_cancel₀
    (Complex.ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N))) hm).symm

theorem gamma0Green_cusp_second_weak_equation (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρpos : tsupport ρ ⊆ Ioi (0 : ℝ)) :
    (∫ y in Ioi (0 : ℝ), deriv (deriv ρ) y • gamma0GlobalCuspConstantTerm N r (gamma0Green N f) y) =
      ∫ y in Ioi (0 : ℝ), (ρ y / y ^ 2) • gamma0GlobalCuspConstantTerm N r (gamma0Green N f) y := by
  obtain ⟨Y, hY, hs⟩ := spectralPositiveTest_exists_height ρ hρc hρpos
  have hρ' := (contDiff_infty_iff_deriv.mp hρ).2
  have hρ'' := (contDiff_infty_iff_deriv.mp hρ').2
  have hs'' : tsupport (deriv (deriv ρ)) ⊆ Ioi Y :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans hs)
  have hκ := spectralPositiveTest_div_pow_contDiff ρ hρ hρpos 2
  have hκc := spectralPositiveTest_div_pow_compact ρ hρc 2
  have hκs := (spectralPositiveTest_div_pow_tsupport ρ 2).trans hs
  rw [gamma0GlobalCuspConstantTerm_compact_test N r (gamma0Green N f) Y hY
      (deriv (deriv ρ)) hρ''.continuous hρc.deriv.deriv hs'',
    gamma0GlobalCuspConstantTerm_compact_test N r (gamma0Green N f) Y hY
      (fun y => ρ y / y ^ 2) hκ.continuous hκc hκs,
    cuspVerticalCompactTest_apply, cuspVerticalCompactTest_apply]
  exact gamma0Green_cusp_second_weak_equation_at_height N r Y hY ρ hρ hρc hρpos hs f hf

theorem gamma0Green_cusp_constantTerm_zero (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    gamma0GlobalCuspConstantTerm N r (gamma0Green N f)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  rw [gamma0Green_apply]
  apply gamma0GlobalCuspConstantTerm_zero_of_second_weak_equation
  intro ρ hρ hρc hρpos
  rw [← gamma0Green_apply]
  exact gamma0Green_cusp_second_weak_equation N r f hf ρ hρ hρc hρpos

theorem gamma0Green_mem_allHeightCuspidalMassSpace (N : ℕ) [NeZero N]
    (f : Gamma0RegionL2 N) (hf : f ∈ gamma0AllHeightCuspidalMassSpace N) :
    gamma0Green N f ∈ gamma0AllHeightCuspidalMassSpace N := by
  rw [mem_gamma0AllHeightCuspidalMassSpace_iff_globalConstantTerm]
  exact fun r => gamma0Green_cusp_constantTerm_zero N r f hf

end ArtinMatthews
