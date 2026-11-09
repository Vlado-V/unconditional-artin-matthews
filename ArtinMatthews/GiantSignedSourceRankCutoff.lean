module

public import ArtinMatthews.GiantSignedSourceContractionBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The equality-rank split uses the original even source moment and
the actual lower prime scale `exp(L^c)`. -/
namespace ArtinMatthews
open Filter
open scoped Topology
noncomputable section

def giantSignedSourceRankCutoff (c scale x : ℝ) : ℕ :=
  ⌈scale * (giantTwoSidedSourceMomentLength x : ℝ) *
    Real.log (Real.log x) / (Real.log x)^c⌉₊

theorem giantSignedSourceRankCutoff_lower {c scale x : ℝ} (hL : 0 < Real.log x) :
    scale * (giantTwoSidedSourceMomentLength x : ℝ) * Real.log (Real.log x) ≤
      (giantSignedSourceRankCutoff c scale x : ℝ) * (Real.log x)^c := by
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hL c)).mp
  exact Nat.le_ceil _

theorem giantSignedSourceRankCutoff_ratio_tendsto {c scale : ℝ}
    (hc : 0 < c) (hscale : 0 ≤ scale) :
    Tendsto (fun x : ℝ => (giantSignedSourceRankCutoff c scale x : ℝ) /
      (giantTwoSidedSourceMomentLength x : ℝ)) atTop (𝓝 0) := by
  have hmain := (((isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero).const_mul scale).comp
    Real.tendsto_log_atTop
  have hceil := tendsto_inv_atTop_zero.comp giantSignedSourceMomentLength_tendsto
  have h := hmain.add hceil
  simp only [mul_zero, zero_add] at h
  apply squeeze_zero' ?_ ?_ h
  · exact Eventually.of_forall (fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hL hn
    let L := Real.log x
    let n := giantTwoSidedSourceMomentLength x
    have hn0 : 0 < (n : ℝ) := zero_lt_one.trans_le hn
    have hp : 0 < L^c := Real.rpow_pos_of_pos (zero_lt_one.trans_le hL) _
    have hnum : 0 ≤ scale * (n : ℝ) * Real.log L / L^c :=
      div_nonneg (mul_nonneg (mul_nonneg hscale hn0.le) (Real.log_nonneg hL)) hp.le
    change (⌈scale * (n : ℝ) * Real.log L / L^c⌉₊ : ℝ) / (n : ℝ) ≤
      scale * (Real.log L / L^c) + (n : ℝ)⁻¹
    calc
      _ ≤ (scale * (n : ℝ) * Real.log L / L^c + 1) / (n : ℝ) :=
        div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hnum).le hn0.le
      _ = _ := by field_simp

theorem giantSignedSourceRankCutoff_le_fraction {c scale ε : ℝ}
    (hc : 0 < c) (hscale : 0 ≤ scale) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (giantSignedSourceRankCutoff c scale x : ℝ) ≤
      ε * (giantTwoSidedSourceMomentLength x : ℝ) := by
  filter_upwards [
    (giantSignedSourceRankCutoff_ratio_tendsto hc hscale).eventually (Iio_mem_nhds hε),
    giantSignedSourceMomentLength_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hn
  exact ((div_lt_iff₀ (zero_lt_one.trans_le hn)).mp hx).le

end
end ArtinMatthews
