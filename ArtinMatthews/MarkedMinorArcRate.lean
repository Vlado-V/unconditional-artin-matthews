module

public import ArtinMatthews.MarkedBonferroniTail


set_option backward.privateInPublic true
@[expose] public section

/-! The clean determinant budget has every logarithmic saving, uniformly in
the actual marking-band scale window. The denominator exponent is chosen
from G alone; fixed constants affect only the threshold. -/
namespace ArtinMatthews
open Filter
open scoped Topology

noncomputable def markedMinorCleanRate (Y Q C : ℝ) : ℝ :=
  (12*C+4)*(1+Real.log (2*Y))/Q +
    26*C*Y^(-1/10 : ℝ)*(1+Real.log (2*Y))

noncomputable def markedMinorRateMajorant (G C D L : ℝ) : ℝ :=
  ((12*C+4)*D)*L^(-G-1) +
    (26*C*D)*L*Real.exp (-(1/10 : ℝ)*L^(1/10 : ℝ))

/-- A bound depending only on `L` dominates the actual budget for every
scale between the smallest and largest permitted marking-band scales. -/
theorem marked_minor_clean_rate_le {G C H L Y : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hYlo : Real.exp (L^(1/10 : ℝ)) ≤ Y)
    (hYhi : Y ≤ Real.exp (H*L^(1/5 : ℝ))) :
    markedMinorCleanRate Y (L^(G+2)) C ≤
      markedMinorRateMajorant G C (H+2) L := by
  have hLp : 0 < L := by linarith
  have hCp : 0 < C := by linarith
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hpow : L^(1/5 : ℝ) ≤ L := by
    have hh := Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1/5:ℝ)≤1)
    simpa only [Real.rpow_one] using hh
  have hlogY : Real.log Y ≤ H*L^(1/5 : ℝ) := (Real.log_le_iff_le_exp hYp).mpr hYhi
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hlog : 1+Real.log (2*Y) ≤ (H+2)*L := by
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hYp.ne']
    nlinarith
  have hlog0 : 0 ≤ 1+Real.log (2*Y) := by
    have hy1 : 1 ≤ Y := (Real.one_le_exp (by positivity)).trans hYlo
    have hh := Real.log_nonneg (show 1 ≤ 2*Y by linarith)
    linarith
  have hneg : Y^(-1/10 : ℝ) ≤ Real.exp (-(1/10 : ℝ)*L^(1/10 : ℝ)) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hYlo
      (by norm_num : (-1/10 : ℝ)≤0)
    rw [← Real.exp_mul] at hh
    convert hh using 1; congr 1; ring
  have hid : L/(L^(G+2)) = L^(-G-1) := by
    have hh := Real.rpow_sub hLp (1:ℝ) (G+2)
    rw [Real.rpow_one] at hh
    simpa only [show (1:ℝ)-(G+2) = -G-1 by ring] using hh.symm
  unfold markedMinorCleanRate markedMinorRateMajorant
  apply add_le_add
  · calc
      _ ≤ (12*C+4)*((H+2)*L)/(L^(G+2)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog (by positivity)) (by positivity)
      _ = ((12*C+4)*(H+2))*(L/(L^(G+2))) := by ring
      _ = _ := by rw [hid]
  · calc
      _ ≤ 26*C*Real.exp (-(1/10 : ℝ)*L^(1/10 : ℝ))*((H+2)*L) := by
        gcongr
      _ = _ := by ring

/-- The uniform scalar majorant saves every chosen logarithmic power. -/
theorem marked_minor_majorant_tendsto (G C D : ℝ) :
    Tendsto (fun L : ℝ => L^G*markedMinorRateMajorant G C D L) atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul ((12*C+4)*D)
  have h₂ := (rpow_mul_exp_neg_rpow_tendsto (G+1)
    (by norm_num : (0:ℝ)<1/10) (by norm_num : (0:ℝ)<1/10)).const_mul (26*C*D)
  have hh := h₁.add h₂
  simp only [mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  unfold markedMinorRateMajorant
  have ha : L^G*L^(-G-1)=L^(-1 : ℝ) := by rw [← Real.rpow_add hL]; congr 1; ring
  have hb : L^G*L = L^(G+1) := by rw [Real.rpow_add hL,Real.rpow_one]
  rw [← ha,← hb]
  ring

/-- Uniform clean minor decay. The fixed exponent `G+2` is independent of
all marking-band exponents and of the fixed scale-window constants. -/
theorem marked_minor_clean_rate_eventually (G : ℝ) {C H : ℝ}
    (hC : 1 ≤ C) (hH : 1 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ Y : ℝ,
      Real.exp (L^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*L^(1/5 : ℝ)) →
      markedMinorCleanRate Y (L^(G+2)) C ≤ L^(-G) := by
  have hsmall := (marked_minor_majorant_tendsto G C (H+2)).eventually
    (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with L hsmall hL Y hYlo hYhi
  have hLp : 0 < L := by linarith
  have hpowp : 0 < L^G := Real.rpow_pos_of_pos hLp _
  have hb := marked_minor_clean_rate_le (G := G) hC hH hL hYlo hYhi
  have hh := mul_le_mul_of_nonneg_left hb hpowp.le
  have hid : L^G*L^(-G)=1 := by rw [← Real.rpow_add hLp]; simp
  apply (mul_le_mul_iff_of_pos_left hpowp).mp
  rw [hid]
  exact hh.trans hsmall.le


/-- The actual logarithmic major-arc cutoff lies below every allowed marking
scale. Its exponent is fixed before the number of marking groups is chosen. -/
theorem marked_minor_logarithmic_cutoff {A : ℝ} (hA : 0 < A) :
    ∀ᶠ L : ℝ in atTop,
      1 ≤ L^A ∧ L^A ≤ Real.exp (L^(1/10 : ℝ)) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/10)).bound
    (show (0:ℝ)<1/A by positivity)
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with L hh hL
  have hLp : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hpow : 0 ≤ L^(1/10 : ℝ) := Real.rpow_nonneg hLp.le _
  simp only [Real.norm_eq_abs,abs_of_nonneg hlog,abs_of_nonneg hpow] at hh
  refine ⟨Real.one_le_rpow hL hA.le,?_⟩
  rw [Real.rpow_def_of_pos hLp]
  apply Real.exp_le_exp.mpr
  have hlog' : Real.log L ≤ L^(1/10 : ℝ)/A := by
    convert hh using 1; ring
  have hm := (le_div_iff₀ hA).mp hlog'
  nlinarith

end ArtinMatthews
