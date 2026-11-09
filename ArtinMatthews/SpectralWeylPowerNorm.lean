module

public import ArtinMatthews.SpectralWeylPowerIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! The folded power majorant gives a bound uniform in the positive modulus.
The compact second profile and its positive lower support remain explicit. -/

noncomputable section
open Set MeasureTheory Filter
namespace ArtinMatthews

theorem spectralWeylPhysicalBilinear_power_norm {X b B M : ℝ}
    (hX : 0 < X) (hb : 0 < b) (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (s t : ℝ) (f g : ℝ → ℂ) (hfm : Measurable f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgp : tsupport g ⊆ Ioi (0 : ℝ))
    (hglo : ∀ x ∈ tsupport g, b ≤ x)
    (hf : ∀ z, 0 < z → ‖f z‖ ≤ M*z^B) :
    ‖spectralWeylPhysicalBilinear s t f g X‖ ≤
      ((4/X)*M*(X^2/(4*b))^B)*
        ((∫ x, ‖g x‖ ∂spectralKLPhysicalMeasure)*∫ u in Ioo (0 : ℝ) 1, (1-u)^(B-1)) := by
  let C := (4/X)*M*(X^2/(4*b))^B
  have hi := ((spectralKLPhysical_compact_integrable g hg hgc hgp).norm.const_mul C).mul_prod
    (spectralFoldEndpointPower_integrable hB)
  have hpos : ∀ᵐ q ∂spectralWeylFoldMeasure, 0 < q.1 ∧ q.2 ∈ Ioo (0 : ℝ) 1 := by
    unfold spectralWeylFoldMeasure
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [spectralKLPositiveWeightMeasure_ae_pos (fun x => x⁻¹)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact ⟨hx,hu⟩
  have hbnd : ∀ᵐ q ∂spectralWeylFoldMeasure,
      ‖spectralWeylFoldDensity s t f g X q‖ ≤ (C*‖g q.1‖)*(1-q.2)^(B-1) := by
    filter_upwards [hpos] with q hq
    convert spectralWeylFoldDensity_compact_power_bound hX hb hq.2 hB hB₁ hM s t q.1 hq.1
      f g hf hglo using 1
    dsimp only [C]
    ring
  rw [spectralWeylPhysicalBilinear_fold hX s t f g hfm hg.measurable
    (spectralWeylFoldDensity_power_integrable hX hB hB₁ hM s t f g hfm hg hgc hgp hf)]
  refine (norm_integral_le_of_norm_le hi hbnd).trans_eq ?_
  rw [integral_prod_mul (fun x : ℝ => C*‖g x‖) (fun u : ℝ => (1-u)^(B-1)),integral_const_mul]
  dsimp only [C]
  ring

theorem spectralWeyl_power_prefactor {X b : ℝ} (hX : 0 < X) (hb : 0 < b) (B M J : ℝ) :
    ((4/X)*M*(X^2/(4*b))^B)*J = (4*M/(4*b)^B*J)*X^(2*B-1) := by
  rw [Real.div_rpow (sq_nonneg X) (by positivity),
    ← Real.rpow_natCast_mul hX.le 2 B,Real.rpow_sub_one hX.ne']
  norm_num only [Nat.cast_ofNat]
  field_simp

theorem spectralWeylPhysicalBilinear_uniform_power_bound {B M : ℝ}
    (hB : 0 < B) (hB₁ : B ≤ 1) (hM : 0 ≤ M)
    (g : ℝ → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgp : tsupport g ⊆ Ioi (0 : ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ X, 0 < X → ∀ s t : ℝ, ∀ f : ℝ → ℂ,
      Measurable f → (∀ z, 0 < z → ‖f z‖ ≤ M*z^B) →
      ‖spectralWeylPhysicalBilinear s t f g X‖ ≤ D*X^(2*B-1) := by
  obtain ⟨b,hb,hglo⟩ := spectral_compact_positive_lower_bound g hgc hgp
  let J := (∫ x, ‖g x‖ ∂spectralKLPhysicalMeasure)*∫ u in Ioo (0 : ℝ) 1, (1-u)^(B-1)
  have hJ : 0 ≤ J := mul_nonneg (integral_nonneg (fun _ => norm_nonneg _))
    (setIntegral_nonneg measurableSet_Ioo (fun u hu => Real.rpow_nonneg (by linarith [hu.2]) _))
  refine ⟨4*M/(4*b)^B*J,by positivity,?_⟩
  intro X hX s t f hfm hf
  exact (spectralWeylPhysicalBilinear_power_norm hX hb hB hB₁ hM s t f g hfm hg hgc hgp hglo hf).trans_eq
    (spectralWeyl_power_prefactor hX hb B M J)

end ArtinMatthews
