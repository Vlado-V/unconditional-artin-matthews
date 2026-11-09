module

public import ArtinMatthews.SourceLocalMultiplicativeMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! Finiteness on compacts and positivity on opens are proved for the
literal density measure. The Bochner integral bridge fixes its scale. -/

namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory Set Topology
open scoped NumberField ENNReal NNReal
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

local notation "k" => P.adicCompletion K

theorem sourceLocalMulDensity_support :
    Function.support (sourceLocalMulDensity K P) = ({0} : Set k)ᶜ := by
  ext x
  simp [sourceLocalMulDensity, Function.mem_support]

theorem sourceLocalMulMeasure_isHaar : (sourceLocalMulMeasure K P).IsHaarMeasure := by
  let μ := sourceLocalSelfDual K P
  let : μ.IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  have hv : IsOpenEmbedding (Units.val : kˣ → k) := IsOpenUnits.isOpenEmbedding_unitsVal
  refine
    { toIsMulLeftInvariant := sourceLocalMulMeasure_isMulLeftInvariant K P
      lt_top_of_isCompact := ?_
      open_pos := ?_ }
  · intro s hs
    have hc : Continuous (fun u : kˣ => ‖((u⁻¹ : kˣ) : k)‖) :=
      continuous_norm.comp (Units.continuous_val.comp continuous_inv)
    obtain ⟨b, hb⟩ := hs.bddAbove_image hc.continuousOn
    have hsm : MeasurableSet (Units.val '' s) := (hs.image hv.continuous).isClosed.measurableSet
    rw [sourceLocalMulMeasure_apply K P s hs.isClosed.measurableSet]
    change (∫⁻ x in Units.val '' s, sourceLocalMulDensity K P x ∂μ) < ∞
    calc
      _ ≤ ∫⁻ _ in Units.val '' s, ENNReal.ofReal b ∂μ := by
        apply setLIntegral_mono' hsm
        rintro x ⟨u, hu, rfl⟩
        rw [sourceLocalMulDensity_eq, ← norm_inv, ← Units.val_inv_eq_inv_val]
        exact ENNReal.ofReal_le_ofReal (hb ⟨u, hu, rfl⟩)
      _ < ∞ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hs.image hv.continuous).measure_lt_top
  · intro s hs hne
    have hsi : Units.val '' s ⊆ ({0} : Set k)ᶜ := by
      rintro x ⟨u, _, rfl⟩
      simpa only [mem_compl_iff, mem_singleton_iff] using u.ne_zero
    rw [sourceLocalMulMeasure_apply K P s hs.measurableSet, ← pos_iff_ne_zero,
      setLIntegral_pos_iff (sourceLocalMulDensity_measurable K P),
      sourceLocalMulDensity_support, inter_eq_right.mpr hsi]
    exact (hv.isOpenMap _ hs).measure_pos μ (hne.image Units.val)

theorem sourceLocalMulMeasure_integral (f : k → ℂ) :
    (∫ u : kˣ, f (u : k) ∂sourceLocalMulMeasure K P) =
      ∫ x : k, ‖x‖⁻¹ • f x ∂sourceLocalSelfDual K P := by
  rw [← (sourceLocalUnits_measurableEmbedding K P).integral_map f,
    sourceLocalMulMeasure_map_val]
  have h : Measurable (fun x : k => ‖x‖₊⁻¹) := continuous_nnnorm.measurable.inv
  change (∫ x, f x ∂(sourceLocalSelfDual K P).withDensity (fun x => (‖x‖₊⁻¹ : ℝ≥0))) = _
  rw [integral_withDensity_eq_integral_smul h]
  congr 1

theorem sourceLocalMulMeasure_integral_punctured (f : k → ℂ) :
    (∫ u : kˣ, f (u : k) ∂sourceLocalMulMeasure K P) =
      ∫ x in ({0} : Set k)ᶜ, ‖x‖⁻¹ • f x ∂sourceLocalSelfDual K P := by
  rw [sourceLocalMulMeasure_integral, ← integral_indicator (measurableSet_singleton (0 : k)).compl]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x = 0 <;> simp [hx]

end
end ArtinMatthews.SourcePhysical
