module

public import ArtinMatthews.SpectralHyperbolicCoordinates
public import Mathlib.MeasureTheory.Function.L2Space


set_option backward.privateInPublic true
@[expose] public section

/-! Exact L² transfer between coordinate bands and the invariant H² measure. -/

noncomputable section
open MeasureTheory Set Filter
open scoped NNReal

namespace ArtinMatthews

/-- Integrability, not just the value of a totalized integral, is preserved by
the exact invariant-density coordinate formula. -/
theorem upperHalfPlane_integrable_coordinates (G : ℝ × ℝ → ℝ) :
    Integrable (fun z : UpperHalfPlane => G (z.re, z.im)) ↔
      IntegrableOn (fun p => G p / p.2 ^ 2) {p : ℝ × ℝ | 0 < p.2} := by
  have hcoe : MeasurePreserving UpperHalfPlane.coe
      (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe,
      UpperHalfPlane.measurableEmbedding_coe.map_comap volume⟩
  let S : Set (ℝ × ℝ) := {p | 0 < p.2}
  have hprod : MeasurePreserving Complex.measurableEquivRealProd
      (volume.restrict (Complex.measurableEquivRealProd ⁻¹' S))
      (volume.restrict S) := by
    refine ⟨Complex.measurableEquivRealProd.measurable, ?_⟩
    rw [← Complex.measurableEquivRealProd.restrict_map,
      Complex.volume_preserving_equiv_real_prod.map_eq]
  rw [UpperHalfPlane.volume_def,
    integrable_withDensity_iff_integrable_smul (by fun_prop)]
  have he : (fun z : UpperHalfPlane =>
      ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) • G (z.re, z.im)) =
      (fun z : UpperHalfPlane => G (z.re, z.im) / z.im ^ 2) := by
    funext z
    simp only [NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_mk, smul_eq_mul]
    ring
  rw [he]
  change Integrable ((fun z : ℂ => G (z.re, z.im) / z.im ^ 2) ∘ UpperHalfPlane.coe)
    (volume.comap UpperHalfPlane.coe) ↔ _
  rw [hcoe.integrable_comp_emb UpperHalfPlane.measurableEmbedding_coe]
  convert hprod.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding
    (g := fun p => G p / p.2 ^ 2) using 1
  · rw [UpperHalfPlane.range_coe]
    rfl
  · rfl

/-- On a fixed positive-height band the actual hyperbolic and Euclidean L²
masses are equivalent, with explicit constants.  Actual hyperbolic L²
membership is proved as part of the conclusion. -/
theorem hyperbolic_L2_band_transfer {F : ℝ × ℝ → ℂ} (hF : Measurable F)
    (hfinite : Integrable (fun p => ‖F p‖ ^ 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hband : ∀ p, F p ≠ 0 → a ≤ p.2 ∧ p.2 ≤ b) :
    MemLp (fun z : UpperHalfPlane => F (z.re, z.im)) 2 volume ∧
    (1 / b ^ 2) * (∫ p, ‖F p‖ ^ 2) ≤
      (∫ z : UpperHalfPlane, ‖F (z.re, z.im)‖ ^ 2) ∧
    (∫ z : UpperHalfPlane, ‖F (z.re, z.im)‖ ^ 2) ≤
      (1 / a ^ 2) * ∫ p, ‖F p‖ ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  have hupper (p : ℝ × ℝ) :
      ‖F p‖ ^ 2 / p.2 ^ 2 ≤ (1 / a ^ 2) * ‖F p‖ ^ 2 := by
    by_cases hz : F p = 0
    · simp [hz]
    have hp := hband p hz
    calc
      _ ≤ ‖F p‖ ^ 2 / a ^ 2 := div_le_div_of_nonneg_left (sq_nonneg _)
        (sq_pos_of_pos ha) ((sq_le_sq₀ ha.le (ha.le.trans hp.1)).mpr hp.1)
      _ = _ := by ring
  have hlower (p : ℝ × ℝ) :
      (1 / b ^ 2) * ‖F p‖ ^ 2 ≤ ‖F p‖ ^ 2 / p.2 ^ 2 := by
    by_cases hz : F p = 0
    · simp [hz]
    have hp := hband p hz
    calc
      _ = ‖F p‖ ^ 2 / b ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _)
        (sq_pos_of_pos (ha.trans_le hp.1))
        ((sq_le_sq₀ (ha.le.trans hp.1) hb.le).mpr hp.2)
  have hweight : Integrable (fun p : ℝ × ℝ => ‖F p‖ ^ 2 / p.2 ^ 2) := by
    apply (hfinite.const_mul (1 / a ^ 2)).mono'
      ((hF.norm.pow_const 2).div (measurable_snd.pow_const 2)).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      change ‖‖F p‖ ^ 2 / p.2 ^ 2‖ ≤ (1 / a ^ 2) * ‖F p‖ ^ 2
      rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact hupper p)
  have hzero (p : ℝ × ℝ) (hp : p ∉ {p : ℝ × ℝ | 0 < p.2}) : F p = 0 := by
    by_contra hz
    exact hp (ha.trans_le (hband p hz).1)
  have hmass : (∫ z : UpperHalfPlane, ‖F (z.re, z.im)‖ ^ 2) =
      ∫ p : ℝ × ℝ, ‖F p‖ ^ 2 / p.2 ^ 2 := by
    rw [upperHalfPlane_integral_coordinates (fun p => ‖F p‖ ^ 2)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    simp only [hzero p hp, norm_zero, zero_pow two_ne_zero, zero_div]
  have hactual : Integrable (fun z : UpperHalfPlane => ‖F (z.re, z.im)‖ ^ 2) :=
    (upperHalfPlane_integrable_coordinates (fun p => ‖F p‖ ^ 2)).mpr hweight.integrableOn
  refine ⟨(memLp_two_iff_integrable_sq_norm
    (hF.comp (by fun_prop)).aestronglyMeasurable).mpr hactual, ?_, ?_⟩
  · rw [hmass, ← integral_const_mul]
    exact integral_mono (hfinite.const_mul _) hweight hlower
  · rw [hmass, ← integral_const_mul]
    exact integral_mono hweight (hfinite.const_mul _) hupper

end ArtinMatthews
