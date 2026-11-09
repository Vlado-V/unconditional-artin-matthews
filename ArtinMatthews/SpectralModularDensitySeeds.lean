module

public import ArtinMatthews.SpectralModularDensityPeriodization
public import ArtinMatthews.SpectralGamma0Core


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth compact seeds can be transported to each actual inverse modular
interior.  The normalization `1/2` compensates exactly for the two central
signs in the full arithmetic periodization. -/

noncomputable section
open Set Filter Topology MeasureTheory
open scoped CompactlySupported MatrixGroups ContDiff

namespace ArtinMatthews

/-- Actual real smoothness is preserved by every integral modular pullback. -/
theorem h2_section_smooth_modular_pullback (F : UpperHalfPlane → ℂ)
    (hF : ContDiffOn ℝ ∞ (fun z : ℂ => F (UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im}) (r : SL(2, ℤ)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => F (r • UpperHalfPlane.ofComplex z))
      {z : ℂ | 0 < z.im} := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ r
  let M : ℂ → ℂ := fun z => UpperHalfPlane.num g z / UpperHalfPlane.denom g z
  have hdet : 0 < g.det.val := by
    simp [g, Matrix.SpecialLinearGroup.det_mapGL]
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hMpos {z : ℂ} (hz : 0 < z.im) : 0 < (M z).im := by
    have h := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rw [← UpperHalfPlane.coe_im, UpperHalfPlane.coe_smul_of_det_pos hdet] at h
    exact h
  have hMeq {z : ℂ} (hz : 0 < z.im) :
      UpperHalfPlane.ofComplex (M z) = r • UpperHalfPlane.ofComplex z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have he : M z = ((g • (⟨z, hz⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) :=
      (UpperHalfPlane.coe_smul_of_det_pos hdet (⟨z, hz⟩ : UpperHalfPlane)).symm
    rw [he, UpperHalfPlane.ofComplex_apply]
    rfl
  intro z hz
  have hden : UpperHalfPlane.denom g z ≠ 0 := UpperHalfPlane.denom_ne_zero g ⟨z, hz⟩
  have hMc : ContDiffAt ℂ ∞ M z := by
    dsimp only [M, UpperHalfPlane.num, UpperHalfPlane.denom]
    fun_prop (disch := exact hden)
  have hcomp := (hF.contDiffAt (hopen.mem_nhds (hMpos hz))).comp z
    (hMc.restrict_scalars ℝ)
  apply (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hopen.mem_nhds hz] with x hx
  exact congrArg F (hMeq hx).symm

/-- Pull a compact smooth seed back by the actual modular action. -/
def modularTranslateSmoothSeed (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    h2SmoothCompactSeeds :=
  ⟨{ toFun := fun z => ψ.val (r • z)
     continuous_toFun := ψ.val.continuous.comp
       (continuous_const_smul (Matrix.SpecialLinearGroup.mapGL ℝ r))
     hasCompactSupport' := ψ.val.hasCompactSupport.comp_homeomorph
       (Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)) },
    h2_section_smooth_modular_pullback ψ.val ψ.property r⟩

theorem modularTranslateSmoothSeed_apply (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (z : UpperHalfPlane) :
    (modularTranslateSmoothSeed r ψ).val z = ψ.val (r • z) := rfl

theorem modularTranslateSmoothSeed_support (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo) :
    tsupport (modularTranslateSmoothSeed r ψ).val ⊆
      (fun z : UpperHalfPlane => r • z) ⁻¹' ModularGroup.fdo := by
  change tsupport (ψ.val ∘ Homeomorph.smul (Matrix.SpecialLinearGroup.mapGL ℝ r)) ⊆ _
  rw [tsupport_comp_eq_preimage]
  exact preimage_mono hψ

/-- The genuinely normalized seed for a selected chart. -/
def modularInteriorChartSeed (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds) :
    h2SmoothCompactSeeds :=
  (1 / 2 : ℂ) • modularTranslateSmoothSeed r ψ

theorem modularInteriorChartSeed_support (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo) :
    tsupport (modularInteriorChartSeed r ψ).val ⊆
      (fun z : UpperHalfPlane => r • z) ⁻¹' ModularGroup.fdo := by
  exact (tsupport_smul_subset_right (fun _ : UpperHalfPlane => (1 / 2 : ℂ))
    ((modularTranslateSmoothSeed r ψ).val : UpperHalfPlane → ℂ)).trans
      (modularTranslateSmoothSeed_support r ψ hψ)

/-- The actual periodization of the normalized translated seed recovers the
original data on its selected interior chart. -/
theorem modularInteriorChartSeed_periodization_self (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (ψ : h2SmoothCompactSeeds)
    (hψ : tsupport ψ.val ⊆ ModularGroup.fdo)
    {z : UpperHalfPlane} (hz : z ∈ ModularGroup.fdo) :
    gamma0PoincareSeed N (modularInteriorChartSeed r ψ).val (r⁻¹ • z) = ψ.val z := by
  rw [gamma0PoincareSeed_eq_two_mul_on_interior_chart N _ r
    (modularInteriorChartSeed_support r ψ hψ) hz]
  change 2 * ((1 / 2 : ℂ) * ψ.val (r • (r⁻¹ • z))) = _
  rw [smul_inv_smul]
  ring

end ArtinMatthews
