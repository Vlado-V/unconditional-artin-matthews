module

public import ArtinMatthews.MarkedMemoryOrphanTailDecay
public import ArtinMatthews.MarkedMemoryOrphanParameterBounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual log-squared pending cutoff absorbs a logarithmic saving
whose exponent grows with the original moment length. Fixed positive
prefactors, including the genuine root volume, are retained. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology

theorem markedMemoryMomentLogPower_exp (G : ℝ) {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (Real.log x)^(G*(markedMemoryMomentLength x:ℝ)) ≤
      Real.exp (4*|G| * (Real.log x)^(3/2:ℝ)) := by
  have hL : 0 < Real.log x := by linarith
  have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlog
  have hllhi : Real.log (Real.log x) ≤ Real.log x := by
    linarith [Real.log_le_sub_one_of_pos hL]
  have hn : (markedMemoryMomentLength x:ℝ) ≤ 4*(Real.log x)^(1/2:ℝ) := by
    linarith [(markedMemoryMomentLength_sqrt_bound hlog).1]
  have hp : (Real.log x)^(1/2:ℝ)*Real.log x=(Real.log x)^(3/2:ℝ) := by
    calc
      _ = (Real.log x)^(1/2:ℝ)*(Real.log x)^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hL]; norm_num
  have hc : (markedMemoryMomentLength x:ℝ)*Real.log (Real.log x) ≤
      4*(Real.log x)^(3/2:ℝ) := by
    have hh := mul_le_mul hn hllhi hll (by positivity)
    nlinarith
  have hg := mul_le_mul_of_nonneg_right (le_abs_self G)
    (show 0 ≤ (markedMemoryMomentLength x:ℝ)*Real.log (Real.log x) by positivity)
  have hh := mul_le_mul_of_nonneg_left hc (abs_nonneg G)
  rw [Real.rpow_def_of_pos hL]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem markedMemoryOrphanTailEnvelope_moment_absorb (C F G : ℝ) (hF : 0 ≤ F)
    {x : ℝ} (hlog : 1 ≤ Real.log x) :
    (F*markedMemoryOrphanTailEnvelope C (3/2:ℝ) x)*
        (Real.log x)^(G*(markedMemoryMomentLength x:ℝ)) ≤
      markedMemoryOrphanTailEnvelope (C+F+4*|G|) (3/2:ℝ) x := by
  have hp : 1 ≤ (Real.log x)^(3/2:ℝ) := Real.one_le_rpow hlog (by norm_num)
  have hFe : F ≤ Real.exp (F*(Real.log x)^(3/2:ℝ)) := by
    have he : F ≤ Real.exp F := by linarith [Real.add_one_le_exp F]
    exact he.trans (Real.exp_le_exp.mpr (by nlinarith))
  have henv : 0 ≤ markedMemoryOrphanTailEnvelope C (3/2:ℝ) x := by
    unfold markedMemoryOrphanTailEnvelope
    positivity
  calc
    _ = (F*(Real.log x)^(G*(markedMemoryMomentLength x:ℝ)))*
        markedMemoryOrphanTailEnvelope C (3/2:ℝ) x := by ring
    _ ≤ (Real.exp (F*(Real.log x)^(3/2:ℝ))*
        Real.exp (4*|G| * (Real.log x)^(3/2:ℝ)))*markedMemoryOrphanTailEnvelope C (3/2:ℝ) x :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hFe (markedMemoryMomentLogPower_exp G hlog)
          (Real.rpow_nonneg (by linarith) _) (Real.exp_nonneg _)) henv
    _ = _ := by
      unfold markedMemoryOrphanTailEnvelope
      rw [← mul_div_assoc,← Real.exp_add,← Real.exp_add]
      congr 2
      ring

theorem markedMemoryOrphanTailEnvelope_moment_log_saving (C F G : ℝ) (hF : 0 ≤ F) :
    ∀ᶠ x : ℝ in atTop,F*markedMemoryOrphanTailEnvelope C (3/2:ℝ) x ≤
      (Real.log x)^(-G*(markedMemoryMomentLength x:ℝ)) := by
  filter_upwards [markedMemoryOrphanTailEnvelope_log_saving (C+F+4*|G|) (3/2:ℝ) 0 (by norm_num),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hL : 0 < Real.log x := by linarith
  have hp : 0 < (Real.log x)^(G*(markedMemoryMomentLength x:ℝ)) := Real.rpow_pos_of_pos hL _
  have hh := (markedMemoryOrphanTailEnvelope_moment_absorb C F G hF hlog).trans hx
  simp only [neg_zero,Real.rpow_zero] at hh
  have hd : F*markedMemoryOrphanTailEnvelope C (3/2:ℝ) x ≤
      1/(Real.log x)^(G*(markedMemoryMomentLength x:ℝ)) := (le_div_iff₀ hp).mpr hh
  rw [show -G*(markedMemoryMomentLength x:ℝ)=-(G*(markedMemoryMomentLength x:ℝ)) by ring,
    Real.rpow_neg hL.le]
  simpa only [one_div] using hd

end
end ArtinMatthews
