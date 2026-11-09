module

public import ArtinMatthews.SpectralCuspVerticalConstantTermRepresentative


set_option backward.privateInPublic true
@[expose] public section

/-! Compatibility of the actual constant-term and vertical-derivative
representatives on nested positive-height strips. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups Topology

namespace ArtinMatthews

theorem cuspVerticalMeasure_mono {Y₁ Y₂ : ℝ} (h : Y₁ ≤ Y₂) :
    cuspVerticalMeasure Y₂ ≤ cuspVerticalMeasure Y₁ := by
  unfold cuspVerticalMeasure
  rw [← restrict_withDensity measurableSet_Ioi, ← restrict_withDensity measurableSet_Ioi]
  exact Measure.restrict_mono_set _ (fun _ hx => h.trans_lt hx)

theorem cuspWeightedVerticalMeasure_mono (w : ℝ) {Y₁ Y₂ : ℝ} (h : Y₁ ≤ Y₂) :
    (cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y₂ ≤
      (cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y₁ := by
  intro s
  simp only [Measure.smul_apply]
  exact mul_le_mul_right (cuspVerticalMeasure_mono h s) _

def cuspVerticalLpRestriction (w Y₁ Y₂ : ℝ) (h : Y₁ ≤ Y₂) :
    CuspVerticalL2 w Y₁ →L[ℝ] CuspVerticalL2 w Y₂ :=
  spectralLpMeasureRestriction (cuspWeightedVerticalMeasure_mono w h)

theorem cuspVerticalLpRestriction_ae (w Y₁ Y₂ : ℝ) (h : Y₁ ≤ Y₂)
    (f : CuspVerticalL2 w Y₁) :
    cuspVerticalLpRestriction w Y₁ Y₂ h f
      =ᵐ[(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y₂] f :=
  spectralLpMeasureRestriction_ae (cuspWeightedVerticalMeasure_mono w h) f

theorem cuspWeightedVerticalMeasure_ae_gt (w Y : ℝ) (hY : 0 < Y) :
    ∀ᵐ y ∂(cuspHorizontalMeasure w univ) • cuspVerticalMeasure Y, Y < y :=
  Measure.ae_smul_measure
    ((spectralHorizontal_cuspVertical_ae_iff hY).mpr (ae_restrict_mem measurableSet_Ioi)) _

theorem gamma0CuspConstantTerm_height_restriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (f : Gamma0RegionL2 N) :
    cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h (gamma0CuspConstantTerm N r Y₁ hY₁ f) =
      gamma0CuspConstantTerm N r Y₂ hY₂ f := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq ((cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h).continuous.comp
      (gamma0CuspConstantTerm N r Y₁ hY₁).continuous) (gamma0CuspConstantTerm N r Y₂ hY₂).continuous)
  intro ψ
  change cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h
    (gamma0CuspConstantTerm N r Y₁ hY₁ (gamma0SmoothSeedMass N ψ)) =
      gamma0CuspConstantTerm N r Y₂ hY₂ (gamma0SmoothSeedMass N ψ)
  apply Lp.ext
  have hc₁ := Measure.ae_smul_measure (gamma0CuspConstantTerm_seed_ae N ψ r Y₁ hY₁)
    (cuspHorizontalMeasure (N : ℝ) univ)
  have hc₁' := (Measure.absolutelyContinuous_of_le
    (cuspWeightedVerticalMeasure_mono (N : ℝ) h)).ae_eq hc₁
  have hc₂ := Measure.ae_smul_measure (gamma0CuspConstantTerm_seed_ae N ψ r Y₂ hY₂)
    (cuspHorizontalMeasure (N : ℝ) univ)
  filter_upwards [cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h
    (gamma0CuspConstantTerm N r Y₁ hY₁ (gamma0SmoothSeedMass N ψ)), hc₁', hc₂,
    cuspWeightedVerticalMeasure_ae_gt (N : ℝ) Y₂ hY₂] with y hr hc₁ hc₂ hy
  rw [hr, hc₁, hc₂]
  have he : (fun x : ℝ => gamma0CuspSeedPlaneExtension N ψ r Y₁ (x, y)) =
      (fun x : ℝ => gamma0CuspSeedPlaneExtension N ψ r Y₂ (x, y)) := by
    funext x
    change spectralSectionSmoothExtension Y₁ (gamma0CuspSection N ψ r) (x, y) =
      spectralSectionSmoothExtension Y₂ (gamma0CuspSection N ψ r) (x, y)
    rw [spectralSectionSmoothExtension_eq hY₁ _ (h.trans hy.le),
      spectralSectionSmoothExtension_eq hY₂ _ hy.le]
  unfold cuspHorizontalMean
  rw [he]

theorem gamma0CuspSeedVerticalPlaneExtension_height_eq (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ)
    (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂) (p : ℝ × ℝ) (hp : Y₂ < p.2) :
    gamma0CuspSeedVerticalPlaneExtension N ψ r Y₁ p =
      gamma0CuspSeedVerticalPlaneExtension N ψ r Y₂ p := by
  have he : gamma0CuspSeedPlaneExtension N ψ r Y₁ =ᶠ[𝓝 p]
      gamma0CuspSeedPlaneExtension N ψ r Y₂ := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp] with q hq
    change spectralSectionSmoothExtension Y₁ (gamma0CuspSection N ψ r) q =
      spectralSectionSmoothExtension Y₂ (gamma0CuspSection N ψ r) q
    rw [spectralSectionSmoothExtension_eq hY₁ _ (h.trans hq.le),
      spectralSectionSmoothExtension_eq hY₂ _ hq.le]
  change p.2 • fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y₁) p (0, 1) =
    p.2 • fderiv ℝ (gamma0CuspSeedPlaneExtension N ψ r Y₂) p (0, 1)
  rw [he.fderiv_eq]

theorem gamma0CuspVerticalConstantTerm_height_restriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (u : gamma0EnergySpace N) :
    cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h (gamma0CuspVerticalConstantTerm N r Y₁ hY₁ u) =
      gamma0CuspVerticalConstantTerm N r Y₂ hY₂ u := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_eq ((cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h).continuous.comp
      (gamma0CuspVerticalConstantTerm N r Y₁ hY₁).continuous)
        (gamma0CuspVerticalConstantTerm N r Y₂ hY₂).continuous)
  intro ψ
  change cuspVerticalLpRestriction (N : ℝ) Y₁ Y₂ h
    (gamma0CuspVerticalConstantTerm N r Y₁ hY₁ (gamma0EnergyTest N ψ)) =
      gamma0CuspVerticalConstantTerm N r Y₂ hY₂ (gamma0EnergyTest N ψ)
  apply Lp.ext
  have hc₁ := Measure.ae_smul_measure (gamma0CuspVerticalConstantTerm_seed_ae N ψ r Y₁ hY₁)
    (cuspHorizontalMeasure (N : ℝ) univ)
  have hc₁' := (Measure.absolutelyContinuous_of_le
    (cuspWeightedVerticalMeasure_mono (N : ℝ) h)).ae_eq hc₁
  have hc₂ := Measure.ae_smul_measure (gamma0CuspVerticalConstantTerm_seed_ae N ψ r Y₂ hY₂)
    (cuspHorizontalMeasure (N : ℝ) univ)
  filter_upwards [cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h
    (gamma0CuspVerticalConstantTerm N r Y₁ hY₁ (gamma0EnergyTest N ψ)), hc₁', hc₂,
    cuspWeightedVerticalMeasure_ae_gt (N : ℝ) Y₂ hY₂] with y hr hc₁ hc₂ hy
  rw [hr, hc₁, hc₂]
  unfold cuspHorizontalMean
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x =>
    gamma0CuspSeedVerticalPlaneExtension_height_eq N ψ r Y₁ Y₂ hY₁ hY₂ h (x, y) hy

theorem gamma0CuspConstantTerm_height_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (f : Gamma0RegionL2 N) :
    gamma0CuspConstantTerm N r Y₁ hY₁ f
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y₂]
        gamma0CuspConstantTerm N r Y₂ hY₂ f := by
  have hr := cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h (gamma0CuspConstantTerm N r Y₁ hY₁ f)
  rw [gamma0CuspConstantTerm_height_restriction N r Y₁ Y₂ hY₁ hY₂ h f] at hr
  exact hr.symm

theorem gamma0CuspConstantTermDerivative_height_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y₁ Y₂ : ℝ) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (h : Y₁ ≤ Y₂)
    (u : gamma0EnergySpace N) :
    gamma0CuspConstantTermDerivative N r Y₁ hY₁ u
      =ᵐ[(cuspHorizontalMeasure (N : ℝ) univ) • cuspVerticalMeasure Y₂]
        gamma0CuspConstantTermDerivative N r Y₂ hY₂ u := by
  have hr := cuspVerticalLpRestriction_ae (N : ℝ) Y₁ Y₂ h (gamma0CuspVerticalConstantTerm N r Y₁ hY₁ u)
  rw [gamma0CuspVerticalConstantTerm_height_restriction N r Y₁ Y₂ hY₁ hY₂ h u] at hr
  exact hr.symm.mono fun y hy => congrArg (fun a : ℂ => y⁻¹ • a) hy

end ArtinMatthews
