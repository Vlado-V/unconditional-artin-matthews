module

public import ArtinMatthews.SourceLocalBallMellin


set_option backward.privateInPublic true
@[expose] public section

/-! The finite condition in the source03 sheet estimate. The compact
annulus is bounded by continuity, while the small shells are summed by
the genuine finite-place Haar Mellin integral. -/
namespace ArtinMatthews.SourceReflection

open NumberField IsDedekindDomain MeasureTheory Set Filter
open ArtinMatthews.SourcePhysical
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K
local notation "μMul" => sourceLocalMulMeasure K P

private theorem thetaFinite_annulus_isCompact (n : ℤ) :
    IsCompact (sourceLocalMulBall K P n \ sourceLocalMulBall K P 0) := by
  rw [(IsOpenUnits.isOpenEmbedding_unitsVal (M := k)).isEmbedding.isCompact_iff]
  change IsCompact (Units.val '' ((Units.val ⁻¹' sourceLocalBall K P n) \
    (Units.val ⁻¹' sourceLocalBall K P 0) : Set kˣ))
  rw [← preimage_sdiff, image_preimage_eq_inter_range, sourceLocalUnits_range,
    inter_eq_self_of_subset_left]
  · exact (sourceLocalBall_isCompact K P n).diff (sourceLocalBall_isOpen K P 0)
  · intro x hx
    have h : x ≠ 0 := fun h => hx.2 (by simp [h, sourceLocalBall])
    simpa using h

theorem sourceThetaFiniteFactor_weighted_integrable (f : kˣ → ℂ) (hf : Continuous f)
    (δ σ C : ℝ) (hC : 0 ≤ C) (hσ : -δ < σ) (n : ℤ)
    (hsupp : ∀ u ∉ sourceLocalMulBall K P n, f u = 0)
    (hsmall : ∀ u ∈ sourceLocalMulBall K P 0, ‖f u‖ ≤ C * ‖(u : k)‖ ^ δ) :
    Integrable (fun u : kˣ => ‖f u‖ * ‖(u : k)‖ ^ σ) μMul := by
  have hnorm (u : kˣ) : 0 < ‖(u : k)‖ := norm_pos_iff.mpr u.ne_zero
  have hpow (a : ℝ) : Continuous (fun u : kˣ => ‖(u : k)‖ ^ a) :=
    (continuous_norm.comp Units.continuous_val).rpow_const (fun u => Or.inl (hnorm u).ne')
  let g (u : kˣ) := ‖f u‖ * ‖(u : k)‖ ^ (-δ)
  have hg : Continuous g := hf.norm.mul (hpow _)
  obtain ⟨D, hD⟩ := (thetaFinite_annulus_isCompact K P n).bddAbove_image hg.continuousOn
  let B := max C D
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  have hpt (u : kˣ) (hu : u ∈ sourceLocalMulBall K P n) : ‖f u‖ ≤ B * ‖(u : k)‖ ^ δ := by
    by_cases h0 : u ∈ sourceLocalMulBall K P 0
    · exact (hsmall u h0).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have hDu : g u ≤ D := hD ⟨u, ⟨hu, h0⟩, rfl⟩
      have hDb : ‖f u‖ ≤ D * ‖(u : k)‖ ^ δ := by
        apply (div_le_iff₀ (Real.rpow_pos_of_pos (hnorm u) δ)).mp
        simpa only [g, Real.rpow_neg (hnorm u).le, div_eq_mul_inv] using hDu
      exact hDb.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hM : IntegrableOn (fun u : kˣ => ‖(u : k)‖ ^ (δ + σ)) (sourceLocalMulBall K P n) μMul := by
    have hi := (sourceLocalMellinWeight_integrable_ball K P n ((δ + σ : ℝ) : ℂ) (by
      rw [Complex.ofReal_re]
      linarith)).norm
    refine (integrableOn_congr_fun ?_ (sourceLocalMulBall_measurable K P n)).mp hi
    intro u _
    change ‖(‖(u : k)‖ : ℂ) ^ ((δ + σ : ℝ) : ℂ)‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hnorm u), Complex.ofReal_re]
  let F (u : kˣ) := ‖f u‖ * ‖(u : k)‖ ^ σ
  have hm : Continuous F := hf.norm.mul (hpow σ)
  have hI : IntegrableOn F (sourceLocalMulBall K P n) μMul := by
    apply (hM.const_mul B).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (sourceLocalMulBall_measurable K P n)] with u hu
    change ‖‖f u‖ * ‖(u : k)‖ ^ σ‖ ≤ B * ‖(u : k)‖ ^ (δ + σ)
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_add (hnorm u), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hpt u hu) (by positivity)
  refine ((integrable_indicator_iff (sourceLocalMulBall_measurable K P n)).mpr hI).congr
    (Eventually.of_forall fun u => ?_)
  by_cases hu : u ∈ sourceLocalMulBall K P n
  · exact indicator_of_mem hu _
  · rw [indicator_of_notMem hu]
    simp [hsupp u hu]

end
end ArtinMatthews.SourceReflection
