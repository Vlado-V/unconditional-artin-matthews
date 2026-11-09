module

public import ArtinMatthews.SpectralGamma0EllipticBandIdentification
public import ArtinMatthews.SpectralGamma0EllipticDivergence
public import ArtinMatthews.SpectralAmbientEigenScalar
public import ArtinMatthews.SpectralGamma0EllipticPotentialCoefficient
public import OAI.Analysis.PDE.Weak.Elliptic.Coefficient


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient eigenvector H¹ pair satisfies its smooth-potential equation. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational
namespace ArtinMatthews

private theorem eigen_integral_test_mul_congr {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {S : Set X} (hS : MeasurableSet S)
    (t u v : X → ℝ) (ht : Function.support t ⊆ S) (he : u =ᵐ[μ.restrict S] v) :
    (∫ x, t x*u x ∂μ) = ∫ x, t x*v x ∂μ := by
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hS).mp he] with x hx
  by_cases ht0 : t x = 0
  · rw [ht0,zero_mul,zero_mul]
  · rw [hx (ht ht0)]

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hab : a ≤ b) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

include hab

theorem gamma0AmbientElliptic_second_weak_equation
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v) {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    (χ : (Fin 2 → ℝ) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ spectralEllipticCoordinates ⁻¹'
      spectralEllipticBand (2*(N:ℝ)) c d) :
    let p := gamma0EllipticPair φ ha hφ r L N v
    (∫ x, spectralEllipticPositiveLaplacian χ x * p.1 x) =
      ∫ x, χ x * spectralEllipticPotentialCoefficient φ ha hφ
        (eig) x (p.1 x) := by
  dsimp only
  let S := spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d
  have hS : MeasurableSet S := (spectralEllipticBand_measurable _ _ _).preimage
    spectralEllipticCoordinates.continuous.measurable
  have hstrip : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N:ℝ)) ∧ Y < x 1} :=
    fun x hx => ⟨(hs hx).1,hc.trans_le (hs hx).2.1⟩
  have hts : Function.support (fun p => χ (spectralEllipticCoordinates.symm p)) ⊆
      Ioc 0 (2*(N:ℝ)) ×ˢ Ioi Y := by
    intro p hp
    exact hstrip (subset_tsupport χ hp)
  have hls : Function.support (fun p => spectralEllipticPositiveLaplacian χ
      (spectralEllipticCoordinates.symm p)) ⊆ Ioc 0 (2*(N:ℝ)) ×ˢ Ioi Y := by
    intro p hp
    exact hstrip (spectralEllipticPositiveLaplacian_support χ (subset_tsupport _ hp))
  have he := gamma0AmbientEigen_strip_scalar_weak_laplacian
    N v eig hl hG r Y hY L χ hχ hcχ hstrip
  change (∫ p, (p.2^2*spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p)) •
      L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p)
      ∂cuspStripMeasure (2*(N:ℝ)) Y) =
    eig *
      ∫ p, χ (spectralEllipticCoordinates.symm p) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p)
        ∂cuspStripMeasure (2*(N:ℝ)) Y at he
  rw [cuspStrip_integral_height_cancel _ hY _ _ hls,
    cuspStrip_integral_compact_density _ hY _ _ hts] at he
  rw [← spectralEllipticCoordinates_integral
      (fun p => spectralEllipticPositiveLaplacian χ (spectralEllipticCoordinates.symm p) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p)),
    ← spectralEllipticCoordinates_integral
      (fun p => (p.2^(-2:ℤ)*χ (spectralEllipticCoordinates.symm p)) •
        L (gamma0CuspTwoCellCoordinateRestriction N r Y hY (gamma0EnergyInclusion N v) p))] at he
  simp only [ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul] at he
  have hheight (x : Fin 2 → ℝ) : (spectralEllipticCoordinates x).2 = x 1 := rfl
  simp only [hheight] at he
  have hv := gamma0EllipticMass_band_ae φ ha hab hφ r L N hY hc hplateau
    (gamma0EnergyInclusion N v)
  rw [gamma0EllipticMass_energy φ ha hab hφ r L N] at hv
  have hleft := eigen_integral_test_mul_congr volume hS (spectralEllipticPositiveLaplacian χ)
    _ _ ((subset_tsupport _).trans ((spectralEllipticPositiveLaplacian_support χ).trans hs)) hv
  have hright := eigen_integral_test_mul_congr volume hS (fun x : Fin 2 → ℝ => x 1^(-2:ℤ)*χ x)
    _ _ (by
      intro x hx
      apply hs
      apply subset_tsupport χ
      intro hz
      exact hx (by change x 1^(-2:ℤ)*χ x = 0; rw [hz,mul_zero])) hv
  rw [← hleft,← hright] at he
  refine he.trans ?_
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hz : χ x = 0
    · simp only [hz,mul_zero,zero_mul]
    · have hx : 0 < x 1 := hY.trans (hstrip (subset_tsupport χ hz)).2
      rw [spectralEllipticPotentialCoefficient_apply_eq φ ha hφ _ hx
        (hplateau _ (hs (subset_tsupport χ hz)))]
      simp only [zpow_neg,zpow_ofNat,div_eq_mul_inv]
      ring

theorem gamma0AmbientElliptic_weakDivergence
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v) {Y c d : ℝ}
    (hY : 0 < Y) (hc : Y < c)
    (hplateau : ∀ p ∈ spectralEllipticBand (2*(N:ℝ)) c d, φ p = 1)
    {Ω : Set (Fin 2 → ℝ)}
    (hΩ : Ω ⊆ spectralEllipticCoordinates ⁻¹' spectralEllipticBand (2*(N:ℝ)) c d)
    {M : ℝ} (hM : ∀ x, ‖spectralEllipticPotentialCoefficient φ ha hφ
      (eig) x‖ ≤ M) :
    let p := gamma0EllipticPair φ ha hφ r L N v
    let B := spectralEllipticPotentialCoefficient φ ha hφ (eig)
    WeakDivergenceEquation Ω p.2
      (fieldMultiplierCLM B
        (spectralEllipticPotentialCoefficient_smoothBounded φ ha hφ _).1.continuous.aestronglyMeasurable
        (Eventually.of_forall hM) p.1) := by
  dsimp only
  apply spectralElliptic_weakDivergence_of_second_tests _
    (gamma0EllipticPair_mem_H1Zero φ ha hφ r L N _) _
  intro χ hχ hcχ hs
  have he := gamma0AmbientElliptic_second_weak_equation φ ha hab hφ r L N v eig hl hG hY hc
    hplateau χ hχ hcχ (hs.trans hΩ)
  dsimp only at he
  have hleft : (∫ x, (gamma0EllipticPair φ ha hφ r L N
      v).1 x * spectralEllipticPositiveLaplacian χ x) =
      ∫ x, spectralEllipticPositiveLaplacian χ x * (gamma0EllipticPair φ ha hφ r L N
        v).1 x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun _ => mul_comm _ _
  rw [hleft,he]
  apply integral_congr_ae
  filter_upwards [fieldMultiplierCLM_ae
    (spectralEllipticPotentialCoefficient φ ha hφ (eig))
    (spectralEllipticPotentialCoefficient_smoothBounded φ ha hφ _).1.continuous.aestronglyMeasurable
    (Eventually.of_forall hM)
    (gamma0EllipticPair φ ha hφ r L N v).1] with x hx
  rw [hx]
  ring

end ArtinMatthews
