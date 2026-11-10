module

public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralSectionGradient
public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralSectionGradientPairing
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan


set_option backward.privateInPublic true
@[expose] public section

/-! Actual gradients of normalized single-chart compact periodizations.
The local equalities follow by differentiating the proved genuine
periodization on the open modular interior. -/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem h2SectionGradient_congr_of_eventuallyEq (F G : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) (h : F =ᶠ[𝓝 z] G) :
    h2SectionGradient F z = h2SectionGradient G z := by
  have hc : ContinuousAt UpperHalfPlane.ofComplex (z : ℂ) :=
    (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hc' : Tendsto UpperHalfPlane.ofComplex (𝓝 (z : ℂ)) (𝓝 z) := by
    simpa only [ContinuousAt,UpperHalfPlane.ofComplex_apply] using hc
  have he : (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) =ᶠ[𝓝 (z : ℂ)]
      (fun w : ℂ => G (UpperHalfPlane.ofComplex w)) := h.comp_tendsto hc'
  unfold h2SectionGradient
  rw [he.fderiv_eq]

theorem h2SectionGradient_zero (z : UpperHalfPlane) :
    h2SectionGradient (fun _ => (0 : ℂ)) z = 0 := by
  ext i
  fin_cases i <;> simp [h2SectionGradient]

/-- The selected chart has exactly the actual gradient of the prescribed
smooth interior data after pulling the periodization into that chart. -/
theorem modularInteriorChartSeed_gradient_self (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    h2SectionGradient
      (fun v => gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val (r⁻¹ • v)) z =
      h2SectionGradient ψ.val z := by
  apply h2SectionGradient_congr_of_eventuallyEq
  filter_upwards [ModularGroup.isOpen_fdo.mem_nhds hz] with v hv
  exact modularInteriorChartSeed_periodization_self N r ψ hψ hv

/-- Every other chart has zero actual pulled-back gradient on the modular
interior, as follows from the actual vanishing periodization there. -/
theorem modularInteriorChartSeed_gradient_other (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ))
    (hrs : (r : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ≠ s)
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    h2SectionGradient
      (fun v => gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val (s⁻¹ • v)) z = 0 := by
  rw [← h2SectionGradient_zero z]
  apply h2SectionGradient_congr_of_eventuallyEq
  filter_upwards [ModularGroup.isOpen_fdo.mem_nhds hz] with v hv
  exact gamma0PoincareSeed_eq_zero_of_interior_chart_ne N _ r s
    (modularInteriorChartSeed_support r ψ hψ) hrs hv

/-- Exact complex Dirichlet integrand in the selected chart, with covariance
proved from the actual differential rather than supplied as a form axiom. -/
theorem modularInteriorChartSeed_gradient_pairing_self (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    inner ℂ (h2SectionGradient (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) (r⁻¹ • z))
      (h2SectionGradient F (r⁻¹ • z)) =
      inner ℂ (h2SectionGradient ψ.val z)
        (h2SectionGradient (fun v => F (r⁻¹ • v)) z) := by
  have hdet : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹).det.val := by
    simp [Matrix.SpecialLinearGroup.det_mapGL]
  have hcov := h2SectionGradient_inner_pullback
    (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) F
    (gamma0PoincareSeed_smooth N _ (modularInteriorChartSeed r ψ).property) hF
    (Matrix.SpecialLinearGroup.mapGL ℝ r⁻¹) hdet z
  change inner ℂ
    (h2SectionGradient (fun v => gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val (r⁻¹ • v)) z)
    (h2SectionGradient (fun v => F (r⁻¹ • v)) z) =
    inner ℂ (h2SectionGradient (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) (r⁻¹ • z))
      (h2SectionGradient F (r⁻¹ • z)) at hcov
  rw [← hcov]
  rw [modularInteriorChartSeed_gradient_self N r ψ hψ hz]

/-- Every off-diagonal chart contributes zero to the actual complex
Dirichlet pairing of the normalized compact interior test. -/
theorem modularInteriorChartSeed_gradient_pairing_other (N : ℕ) [NeZero N]
    (r s : SL(2, ℤ))
    (hrs : (r : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) ≠ s)
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun w : ℂ => F (UpperHalfPlane.ofComplex w))
      {w : ℂ | 0 < w.im})
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    inner ℂ (h2SectionGradient (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) (s⁻¹ • z))
      (h2SectionGradient F (s⁻¹ • z)) = 0 := by
  have hdet : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹).det.val := by
    simp [Matrix.SpecialLinearGroup.det_mapGL]
  have hcov := h2SectionGradient_inner_pullback
    (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) F
    (gamma0PoincareSeed_smooth N _ (modularInteriorChartSeed r ψ).property) hF
    (Matrix.SpecialLinearGroup.mapGL ℝ s⁻¹) hdet z
  change inner ℂ
    (h2SectionGradient (fun v => gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val (s⁻¹ • v)) z)
    (h2SectionGradient (fun v => F (s⁻¹ • v)) z) =
    inner ℂ (h2SectionGradient (gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val) (s⁻¹ • z))
      (h2SectionGradient F (s⁻¹ • z)) at hcov
  rw [← hcov,modularInteriorChartSeed_gradient_other N r s hrs ψ hψ hz,inner_zero_left]

end ArtinMatthews
