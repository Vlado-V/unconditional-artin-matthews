module

public import ArtinMatthews.MarkedMemoryActualCapacityCorrection
public import ArtinMatthews.MarkedPhysicalCoordinateGoodVolume


set_option backward.privateInPublic true
@[expose] public section

/-! The exact full-band baseline product and normalized root measure
cost in the quantitative capped boundary estimate. -/

noncomputable section
namespace ArtinMatthews
open Filter MeasureTheory
open scoped BigOperators

theorem markedMemoryActualBaselineProduct_bounds
    {J : Type*} [Fintype J] (e : J → ℝ) (he : ∀ j,(1/10:ℝ)≤e j) :
    ∀ᶠ x : ℝ in atTop,∀ q : ℝ,0≤q → q≤1 →
      0≤(∏ j,∏ p : markedRawActualPrimeBand e x j,
        markedMemoryBaseline q (markedMemoryMomentLength x) p.1) ∧
      (∏ j,∏ p : markedRawActualPrimeBand e x j,
        markedMemoryBaseline q (markedMemoryMomentLength x) p.1)≤1 := by
  filter_upwards [markedMemoryMomentLength_prime_small_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hn hlog
  intro q hq₀ hq₁
  apply markedMemoryPathBaselineProduct_bounds q hq₀ hq₁
  intro j p
  have hm : (p.1:ℕ)∈markedLogPowerBand (e j) x := (mem_markedRawPrimeBand _ p.1).mp p.2
  exact hn _ (marked_band_common_lower (he j) hlog hm)

theorem markedNormalizedRoot_integral_norm_le
    (f : (ℝ × (ℝ × ℝ)) → ℂ) (C : ℝ)
    (hf : ∀ p∈markedRootBoxDomain,‖f p‖≤C) :
    ‖∫ p,f p ∂markedNormalizedRootMeasure‖≤15*C := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  have hae : ∀ᵐ p ∂markedNormalizedRootMeasure,p∈markedRootBoxDomain := by
    unfold markedNormalizedRootMeasure markedRootBoxDomain
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × (ℝ × ℝ) => p.1∈Set.Icc (0:ℝ) 1 ∧
        p.2.1∈Set.Icc (1:ℝ) 16 ∧ p.2.2∈Set.Icc (1:ℝ) 2) (by measurability)).2
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with r hr
    simp only [hr,true_and]
    apply (Measure.ae_prod_iff_ae_ae
      (p := fun p : ℝ × ℝ => p.1∈Set.Icc (1:ℝ) 16 ∧ p.2∈Set.Icc (1:ℝ) 2)
      (by measurability)).2
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with a ha
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with b hb
    exact ⟨ha,hb⟩
  have h := norm_integral_le_of_norm_le_const (hae.mono (fun p hp => hf p hp))
  simpa only [Measure.real,markedNormalizedRootMeasure_univ,ENNReal.toReal_ofNat,mul_comm] using h

end ArtinMatthews
