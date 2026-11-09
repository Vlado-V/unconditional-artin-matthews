module

public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralCuspVerticalTesting
public import ArtinMatthews.SpectralCuspPositiveTestWeights
public import ArtinMatthews.SpectralCuspHorizontalMeanWeak
public import ArtinMatthews.SpectralCuspWeakRegularity


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine first weak derivative identity for the completed constant
term. Continuity of compact-test functionals transfers the smooth
horizontal-mean integration by parts to the actual energy completion. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem spectralTest_setIntegral_eq_integral (κ : ℝ → ℝ) (s : Set ℝ)
    (hs : tsupport κ ⊆ s) (F : ℝ → ℂ) :
    (∫ y in s, κ y • F y) = ∫ y, κ y • F y := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)), zero_smul]

theorem gamma0CuspConstantTerm_weak_verticalDerivative_at_height (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioi Y) (u : gamma0EnergySpace N) :
    (∫ y in Ioi Y, deriv ρ y • gamma0CuspConstantTerm N r Y hY
        (gamma0EnergyInclusion N u) y) =
      -(∫ y in Ioi Y, (ρ y / y) • gamma0CuspVerticalConstantTerm N r Y hY u y) := by
  have hw : 0 < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  have hρpos : tsupport ρ ⊆ Ioi (0 : ℝ) := fun _ hy => hY.trans (hρs hy)
  have hκ : Continuous (fun y => ρ y / y) := by
    simpa only [pow_one] using (spectralPositiveTest_div_pow_contDiff ρ hρ hρpos 1).continuous
  have hκc : HasCompactSupport (fun y => ρ y / y) := by
    simpa only [pow_one] using spectralPositiveTest_div_pow_compact ρ hρc 1
  let T := cuspVerticalCompactTest hw hY (deriv ρ)
    (hρ.continuous_deriv (by simp)) hρc.deriv
  let S := cuspVerticalCompactTest hw hY (fun y => ρ y / y) hκ hκc
  have he : T (gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N u)) =
      -S (gamma0CuspVerticalConstantTerm N r Y hY u) := by
    apply isClosed_property (gamma0EnergyTest_dense N)
      (isClosed_eq (T.continuous.comp ((gamma0CuspConstantTerm N r Y hY).continuous.comp
        (gamma0EnergyInclusion N).continuous))
        (continuous_neg.comp (S.continuous.comp (gamma0CuspVerticalConstantTerm N r Y hY).continuous)))
    intro ψ
    change T (gamma0CuspConstantTerm N r Y hY
      (gamma0EnergyInclusion N (gamma0EnergyTest N ψ))) =
        -S (gamma0CuspVerticalConstantTerm N r Y hY (gamma0EnergyTest N ψ))
    rw [gamma0EnergyInclusion_test]
    change cuspVerticalCompactTest hw hY (deriv ρ) _ _ _ =
      -cuspVerticalCompactTest hw hY (fun y => ρ y / y) hκ hκc _
    rw [cuspVerticalCompactTest_apply, cuspVerticalCompactTest_apply]
    let F := gamma0CuspSeedPlaneExtension N ψ r Y
    have hF : ContDiff ℝ ∞ F :=
      spectralSectionSmoothExtension_contDiff hY _ (gamma0CuspSection_smooth N ψ r)
    have hc := (spectralHorizontal_cuspVertical_ae_iff hY).mp
      (gamma0CuspConstantTerm_seed_ae N ψ r Y hY)
    have hd := (spectralHorizontal_cuspVertical_ae_iff hY).mp
      (gamma0CuspConstantTermDerivative_seed_ae N ψ r Y hY)
    have hleft : (∫ y in Ioi Y, deriv ρ y • gamma0CuspConstantTerm N r Y hY
        (gamma0SmoothSeedMass N ψ) y) =
        ∫ y in Ioi Y, deriv ρ y • cuspHorizontalMean (N : ℝ) F y := by
      apply integral_congr_ae
      exact hc.mono fun y hy => by dsimp only; rw [hy]
    have hright : (∫ y in Ioi Y, (ρ y / y) • gamma0CuspVerticalConstantTerm N r Y hY
        (gamma0EnergyTest N ψ) y) =
        ∫ y in Ioi Y, ρ y • cuspHorizontalMean (N : ℝ)
          (fun p => fderiv ℝ F p (0, 1)) y := by
      apply integral_congr_ae
      filter_upwards [hd] with y hy
      rw [div_eq_mul_inv, mul_smul]
      change ρ y • gamma0CuspConstantTermDerivative N r Y hY (gamma0EnergyTest N ψ) y = _
      rw [hy]
    rw [hleft, hright,
      spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi Y) (tsupport_deriv_subset.trans hρs),
      spectralTest_setIntegral_eq_integral ρ (Ioi Y) hρs]
    exact cuspHorizontalMean_weak_verticalDerivative hF (N : ℝ) ρ hρ hρc
  simpa only [T, S, cuspVerticalCompactTest_apply] using he

theorem gamma0GlobalCuspConstantTerm_weak_derivative (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    SpectralCuspWeakRegularity.PositiveWeakDerivative
      (gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u))
      (gamma0GlobalCuspConstantTermDerivative N r u) := by
  intro ρ hρ hρc hρs
  obtain ⟨Y, hY, hs⟩ := spectralPositiveTest_exists_height ρ hρc hρs
  have hc := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTerm_ae N r (gamma0EnergyInclusion N u) Y hY)
  have hg := (spectralCuspVerticalL2_ae_iff (Nat.cast_pos.mpr (NeZero.pos N)) hY).mp
    (gamma0GlobalCuspConstantTermDerivative_ae N r u Y hY)
  have h := gamma0CuspConstantTerm_weak_verticalDerivative_at_height N r Y hY ρ hρ hρc hs u
  have hcint : (∫ y in Ioi Y, deriv ρ y • gamma0GlobalCuspConstantTerm N r
      (gamma0EnergyInclusion N u) y) =
      ∫ y in Ioi Y, deriv ρ y • gamma0CuspConstantTerm N r Y hY (gamma0EnergyInclusion N u) y := by
    apply integral_congr_ae
    exact hc.mono fun y hy => by dsimp only; rw [hy]
  have hgint : (∫ y in Ioi Y, ρ y • gamma0GlobalCuspConstantTermDerivative N r u y) =
      ∫ y in Ioi Y, (ρ y / y) • gamma0CuspVerticalConstantTerm N r Y hY u y := by
    apply integral_congr_ae
    filter_upwards [hg] with y hy
    rw [hy]
    simp only [gamma0CuspConstantTermDerivative, div_eq_mul_inv, mul_smul]
  rw [← hcint, ← hgint] at h
  rw [spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi Y) (tsupport_deriv_subset.trans hs),
    spectralTest_setIntegral_eq_integral ρ (Ioi Y) hs] at h
  rw [spectralTest_setIntegral_eq_integral (deriv ρ) (Ioi (0 : ℝ))
      (tsupport_deriv_subset.trans hρs),
    spectralTest_setIntegral_eq_integral ρ (Ioi (0 : ℝ)) hρs]
  exact h

end ArtinMatthews
