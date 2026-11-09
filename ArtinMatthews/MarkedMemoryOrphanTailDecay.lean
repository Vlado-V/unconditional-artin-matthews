module

public import ArtinMatthews.MarkedMinorArcDirtyScalar


set_option backward.privateInPublic true
@[expose] public section

/-! The original B=ceil(log(x)^2) orphan threshold absorbs every
exp(C*log(x)^a) cost with a<2, including any prescribed logarithmic
saving. This is a numerical envelope, not an assumed path-cost bound. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped Topology

def markedMemoryOrphanTailEnvelope (C a x : ℝ) : ℝ :=
  Real.exp (C*(Real.log x)^a)/(2:ℝ)^(markedDirtyMemoryCutoff x/2+1)

theorem markedMemoryOrphanTailEnvelope_le_gaussian (C a : ℝ) (ha : a<2) :
    ∀ᶠ x : ℝ in atTop,
      markedMemoryOrphanTailEnvelope C a x ≤
        Real.exp (-(Real.log 2/4)*(Real.log x)^2) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have ht := (tendsto_rpow_atTop (sub_pos.mpr ha)).comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop (4*|C|/Real.log 2)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  change 4*|C|/Real.log 2≤(Real.log x)^(2-a) at hx
  have hL : 0<Real.log x := by linarith
  have hsplit : (Real.log x)^a*(Real.log x)^(2-a)=(Real.log x)^2 := by
    rw [← Real.rpow_add hL,show a+(2-a)=(2:ℝ) by ring,Real.rpow_two]
  have hc : C*(Real.log x)^a≤(Real.log 2/4)*(Real.log x)^2 := by
    have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hlog2).mp hx)
      (Real.rpow_nonneg hL.le a)
    have hh' : (Real.log x)^a*4*|C|≤(Real.log x)^2*Real.log 2 := by
      simpa only [← mul_assoc,hsplit] using hh
    have hC := le_abs_self C
    have hmul := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hL.le a)
    nlinarith [hh']
  have hn : markedDirtyMemoryCutoff x≤2*(markedDirtyMemoryCutoff x/2+1) := by omega
  have hnR : (markedDirtyMemoryCutoff x:ℝ)≤2*((markedDirtyMemoryCutoff x/2+1:ℕ):ℝ) := by exact_mod_cast hn
  have hceil : (Real.log x)^2≤(markedDirtyMemoryCutoff x:ℝ) := Nat.le_ceil _
  have hpow : (2:ℝ)^(markedDirtyMemoryCutoff x/2+1)=
      Real.exp (((markedDirtyMemoryCutoff x/2+1:ℕ):ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [markedMemoryOrphanTailEnvelope,hpow,← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem markedMemoryOrphanTailEnvelope_log_tendsto (C a G : ℝ) (ha : a<2) :
    Tendsto (fun x : ℝ => (Real.log x)^G*markedMemoryOrphanTailEnvelope C a x)
      atTop (nhds 0) := by
  have hlog2 : 0<Real.log 2/4 := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  have ht := (rpow_mul_exp_neg_rpow_tendsto G (by norm_num : (0:ℝ)<2) hlog2).comp Real.tendsto_log_atTop
  simp only [Function.comp_def,Real.rpow_two] at ht
  apply squeeze_zero'
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx
    unfold markedMemoryOrphanTailEnvelope
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity)
  · filter_upwards [markedMemoryOrphanTailEnvelope_le_gaussian C a ha,
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
    exact mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg (by linarith) _)
  · exact ht

theorem markedMemoryOrphanTailEnvelope_log_saving (C a G : ℝ) (ha : a<2) :
    ∀ᶠ x : ℝ in atTop,markedMemoryOrphanTailEnvelope C a x≤(Real.log x)^(-G) := by
  filter_upwards [(markedMemoryOrphanTailEnvelope_log_tendsto C a G ha).eventually
      (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hL : 0<Real.log x := by linarith
  have hp : 0<(Real.log x)^G := Real.rpow_pos_of_pos hL G
  have hh : markedMemoryOrphanTailEnvelope C a x≤1/(Real.log x)^G :=
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hx.le)
  simpa only [Real.rpow_neg hL.le,one_div] using hh

end
end ArtinMatthews
