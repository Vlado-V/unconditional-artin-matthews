module

public import ArtinMatthews.StandardLocalHaarScaling


set_option backward.privateInPublic true
@[expose] public section

/-! Actual arbitrary local dilations shift the integer valuation radius
by the logarithm of the literal valuation. The Haar factor is exactly
the normalized Mathlib finite-place absolute value. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (P : HeightOneSpectrum (𝓞 K))

theorem sourceLocalNorm_eq_zpow (x : P.adicCompletion K) (hx : x ≠ 0) :
    ‖x‖ = (Ideal.absNorm P.asIdeal : ℝ) ^ WithZero.log (sourceLocalValuation K P x) := by
  have hv : sourceLocalValuation K P x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  simp only [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply
    (NumberField.HeightOneSpectrum.absNorm_ne_zero P) hv, NNReal.coe_zpow, NNReal.coe_natCast]

theorem sourceLocalBall_div_mem (n : ℤ) (t : (P.adicCompletion K)ˣ) (x : P.adicCompletion K) :
    x / (t : P.adicCompletion K) ∈ sourceLocalBall K P n ↔
      x ∈ sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K))) := by
  let v := sourceLocalValuation K P
  have hv : v (t : P.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr t.ne_zero
  change v (x / (t : P.adicCompletion K)) ≤ WithZero.exp n ↔
    v x ≤ WithZero.exp (n + WithZero.log (v (t : P.adicCompletion K)))
  rw [map_div₀, div_le_iff₀ (pos_iff_ne_zero.mpr hv), WithZero.exp_add, WithZero.exp_log hv]

theorem sourceLocalBall_dilation_volume (μ : Measure (P.adicCompletion K)) [μ.IsAddHaarMeasure]
    (n : ℤ) (t : (P.adicCompletion K)ˣ) :
    μ.real (sourceLocalBall K P (n + WithZero.log (sourceLocalValuation K P (t : P.adicCompletion K)))) =
      ‖(t : P.adicCompletion K)‖ * μ.real (sourceLocalBall K P n) := by
  rw [sourceLocalBall_volume_scaling K P μ, sourceLocalBall_volume_scaling K P μ n,
    sourceLocalNorm_eq_zpow K P (t : P.adicCompletion K) t.ne_zero,
    zpow_add₀ (sourceLocalNorm_pos K P).ne']
  ring

end
end ArtinMatthews.SourcePhysical
