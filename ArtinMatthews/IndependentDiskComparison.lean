module

public import ArtinMatthews.IndependentDiskZeros
public import ArtinMatthews.IndependentDiskLog
public import ArtinMatthews.IndependentDiskQuotient

/-! The finite zero sum and the quantitative logarithmic derivative remainder
on the inner disk, with the radii and constants used by the OAI character
estimates. -/

public section

namespace Erdos970

open ArtinMatthews Filter Metric Set
open scoped BigOperators Classical Topology

theorem final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) 1))
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 ((hr1pos.trans hr1_lt_r).trans hr_lt_R1) f).Finite)
    {h_σ : ℂ → ℂ → ℂ}
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 ((hr1pos.trans hr1_lt_r).trans hr_lt_R1) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in 𝓝 σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) r1 \ zerosetKfR R1 ((hr1pos.trans hr1_lt_r).trans hr_lt_R1) f,
      ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
        (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      (16 * r^2 / ((r - r1)^3) +
        1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
  have hR1p := (hr1pos.trans hr1_lt_r).trans hr_lt_R1
  have hRp := hR1p.trans hR1_lt_R
  have hf0 : f 0 ≠ 0 := by rw [h_f_zero]; exact one_ne_zero
  let S := h_finite_zeros.toFinset
  let m : ℂ → ℕ := fun a => (analyticOrderAt f a).toNat
  let G := independentDiskQuotient R S m f h_σ
  let D := independentDiskDenominator R S m
  have hS (a : ℂ) : a ∈ S ↔ a ∈ closedBall (0 : ℂ) R1 ∧ f a = 0 :=
    h_finite_zeros.mem_toFinset
  have hSmall (a : ℂ) (ha : a ∈ S) : ‖a‖ ≤ R1 :=
    mem_closedBall_zero_iff.mp ((hS a).mp ha).1
  have hOuter (a : ℂ) (ha : a ∈ S) : ‖a‖ < R := (hSmall a ha).trans_lt hR1_lt_R
  have hfR : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R) :=
    h_f_analytic.mono (closedBall_subset_closedBall hR.le)
  have hG : AnalyticOnNhd ℂ G (closedBall (0 : ℂ) R) := by
    apply independentDiskQuotient_analytic hfR
    intro a ha
    have h := h_σ_spec a (h_finite_zeros.mem_toFinset.mp ha)
    exact ⟨h.1, h.2.2⟩
  have hzeroS : (0 : ℂ) ∉ S := fun hh => hf0 ((hS 0).mp hh).2
  have hG0 : 1 ≤ ‖G 0‖ :=
    independentDiskQuotient_norm_zero hRp (fun a ha => (hOuter a ha).le) hzeroS h_f_zero
  have hInner : ball (0 : ℂ) r ⊆ closedBall 0 R1 :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hr_lt_R1.le)
  have hInsideOuter : closedBall (0 : ℂ) R1 ⊆ closedBall 0 R :=
    closedBall_subset_closedBall hR1_lt_R.le
  have hGn (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : G w ≠ 0 :=
    independentDiskQuotient_ne_zero hR1p hR1_lt_R hS
      (fun a ha => (h_σ_spec a (h_finite_zeros.mem_toFinset.mp ha)).2.1) (hInner hw)
  have hGb (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : ‖G w‖ ≤ B :=
    independentDiskQuotient_norm_le hRp hOuter hG h_f_bounded (hInsideOuter (hInner hw))
  have hGd : ‖logDeriv G z‖ ≤ (16 * r^2 / (r - r1)^3) * Real.log B :=
    independentDisk_logDeriv_bound hr1pos hr1_lt_r hB
      (hG.mono (hInner.trans hInsideOuter)) hGn hG0 hGb hz.1
  have hzR1 := closedBall_subset_closedBall (hr1_lt_r.trans hr_lt_R1).le hz.1
  have hzS : z ∉ S := fun hh => hz.2 (h_finite_zeros.mem_toFinset.mp hh)
  have hzf : f z ≠ 0 := fun h => hz.2 ⟨hzR1, h⟩
  have hzR := hInsideOuter hzR1
  have hD : ‖logDeriv D z‖ ≤
      (∑ a ∈ S, (m a : ℝ)) * (1 / (R^2 / R1 - R1)) :=
    independentDiskDenominator_logDeriv_bound hR1p hR1_lt_R m hSmall
      (mem_closedBall_zero_iff.mp hzR1)
  have hcount : (∑ a ∈ S, (m a : ℝ)) ≤ (1 / Real.log (R / R1)) * Real.log B :=
    lem_sum_m_rho_bound B R R1 hB hR1p hR1_lt_R hR f h_f_analytic hf0 h_f_zero
      h_finite_zeros h_σ (fun a ha => h_f_bounded a (mem_closedBall_zero_iff.mpr ha)) h_σ_spec
  have hden : 0 < R^2 / R1 - R1 := by
    apply sub_pos.mpr
    apply (lt_div_iff₀ hR1p).mpr
    nlinarith [mul_pos (sub_pos.mpr hR1_lt_R) (add_pos hRp hR1p)]
  have hQ : logDeriv G z = logDeriv f z + logDeriv D z -
      ∑ a ∈ S, (m a : ℂ) / (z - a) :=
    independentDiskQuotient_logDeriv hRp hOuter (mem_closedBall_zero_iff.mp hzR)
      hzS (hfR z hzR).differentiableAt hzf
  have heq : logDeriv f z - (∑ a ∈ S, (m a : ℂ) / (z - a)) =
      logDeriv G z - logDeriv D z := by
    rw [hQ]
    ring
  change ‖logDeriv f z - (∑ a ∈ S, (m a : ℂ) / (z - a))‖ ≤ _
  rw [heq]
  calc
    ‖logDeriv G z - logDeriv D z‖ ≤ ‖logDeriv G z‖ + ‖logDeriv D z‖ := norm_sub_le _ _
    _ ≤ (16 * r^2 / (r - r1)^3) * Real.log B +
        (1 / Real.log (R / R1) * Real.log B) * (1 / (R^2 / R1 - R1)) :=
      add_le_add hGd (hD.trans (mul_le_mul_of_nonneg_right hcount (by positivity)))
    _ = _ := by
      simp only [div_eq_mul_inv, one_mul, mul_inv_rev]
      ring

end Erdos970
