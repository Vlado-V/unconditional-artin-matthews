module

public import ArtinMatthews.SpectralKFrameLogWindow


set_option backward.privateInPublic true
@[expose] public section

/-! Smooth physical tests obtained from the fixed logarithmic window.
The exact substitution retains the measure dx/x and the finite period. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology

namespace ArtinMatthews

def spectralKFramePhysicalTest (ψ χ : ℝ → ℝ) (T x : ℝ) : ℝ :=
  if 0 < x then ψ (Real.log (x/(T/32)))*χ (Real.log (x/(T/32))) else 0

theorem spectralKFramePhysicalTest_support (ψ χ : ℝ → ℝ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T : ℝ) (hT : 0 < T) :
    tsupport (spectralKFramePhysicalTest ψ χ T) ⊆ Icc (T/16) (12*T) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hx0 : 0 < x := by
    by_contra! hx0
    exact hx (by simp only [spectralKFramePhysicalTest,ite_eq_right (not_lt.mpr hx0)])
  let k := T/32
  have hk : 0 < k := by dsimp only [k]; positivity
  have hψ : Real.log (x/k) ∈ Function.support ψ := by
    intro h
    apply hx
    change (if 0 < x then ψ (Real.log (x/k))*χ (Real.log (x/k)) else 0) = 0
    rw [ite_eq_left hx0,h,zero_mul]
  have hlog := hSupp (subset_tsupport ψ hψ)
  have hlo := Real.exp_le_exp.mpr hlog.1
  have hhi := Real.exp_le_exp.mpr hlog.2
  rw [Real.exp_log (by norm_num : (0 : ℝ)<2),Real.exp_log (div_pos hx0 hk)] at hlo
  rw [Real.exp_log (by norm_num : (0 : ℝ)<384),Real.exp_log (div_pos hx0 hk)] at hhi
  have h₁ := (le_div_iff₀ hk).mp hlo
  have h₂ := (div_le_iff₀ hk).mp hhi
  dsimp only [k] at h₁ h₂
  exact ⟨by linarith,by linarith⟩

theorem spectralKFramePhysicalTest_log_support (ψ χ : ℝ → ℝ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T : ℝ) (hT : 0 < T) :
    tsupport (spectralKFramePhysicalTest ψ χ T) ⊆ Ioc (T/32) (24*T) := by
  intro x hx
  obtain ⟨h₁,h₂⟩ := spectralKFramePhysicalTest_support ψ χ hSupp T hT hx
  exact ⟨by linarith,by linarith⟩

theorem spectralKFramePhysicalTest_contDiff (ψ χ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T : ℝ) (hT : 0 < T) :
    ContDiff ℝ ∞ (spectralKFramePhysicalTest ψ χ T) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hi : ContDiffAt ℝ ∞ (fun y : ℝ => y/(T/32)) x := contDiffAt_id.div_const _
    have ho : ContDiffAt ℝ ∞ Real.log (x/(T/32)) :=
      Real.contDiffAt_log.mpr (div_ne_zero hx.ne' (by positivity))
    have hlog : ContDiffAt ℝ ∞ (fun y : ℝ => Real.log (y/(T/32))) x := by
      simpa only [Function.comp_def] using ho.comp x hi
    have hp := (hψ.mul hχ).contDiffAt.comp x hlog
    apply hp.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    have hy0 : 0 < y := hy
    simp only [spectralKFramePhysicalTest,ite_eq_left hy0,Function.comp_apply]
  · have hz : x ∉ tsupport (spectralKFramePhysicalTest ψ χ T) := by
      intro h
      have hy := (spectralKFramePhysicalTest_support ψ χ hSupp T hT h).1
      exact hx (lt_of_lt_of_le (by positivity : 0<T/16) hy)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz)

theorem spectralKFramePhysicalTest_compact (ψ χ : ℝ → ℝ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384)) (T : ℝ) (hT : 0 < T) :
    HasCompactSupport (spectralKFramePhysicalTest ψ χ T) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (spectralKFramePhysicalTest_support ψ χ hSupp T hT)

theorem spectralKFramePhysicalTest_scaledExp (ψ χ : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (u : ℝ) :
    spectralKFramePhysicalTest ψ χ T (T/32*Real.exp u) = ψ u*χ u := by
  have hk : 0 < T/32 := by positivity
  have hx := mul_pos hk (Real.exp_pos u)
  rw [spectralKFramePhysicalTest,ite_eq_left hx,show T/32*Real.exp u/(T/32) = Real.exp u by
    field_simp [hk.ne'],Real.log_exp]

theorem spectralKFrame_integral_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (T : ℝ) (hT : 0 < T)
    (hg : ∀ x : ℝ, x ∉ Ioc (T/32) (24*T) → g x = 0) :
    (∫ x : ℝ, g x ∂spectralKLPhysicalMeasure) =
      ∫ u in (0 : ℝ)..spectralKFrameLength, g (T/32*Real.exp u) := by
  let k := T/32
  let S := Ioc k (24*T)
  have hk : 0 < k := by dsimp only [k]; positivity
  have hS : S ⊆ Ioi (0 : ℝ) := fun _ hx => hk.trans hx.1
  have hweight : Measurable (fun x : ℝ => ENNReal.ofReal x⁻¹) := by fun_prop
  have hfin : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ENNReal.ofReal x⁻¹ < ⊤ :=
    Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  calc
    _ = ∫ x in Ioi (0 : ℝ), x⁻¹ • g x := by
      unfold spectralKLPhysicalMeasure spectralKLPositiveWeightMeasure
      rw [integral_withDensity_eq_integral_toReal_smul hweight hfin g]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hx.le)]
    _ = ∫ x in S, x⁻¹ • g x := by
      rw [← Measure.restrict_restrict_of_subset hS]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hg x hx,smul_zero])).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le spectralKFrameLength_pos.le,
        spectral_scaledExp_Ioc_integral g hk 0 spectralKFrameLength,Real.exp_zero,mul_one]
      have he : k*Real.exp spectralKFrameLength = 24*T := by
        dsimp only [k,spectralKFrameLength]
        rw [Real.exp_log (by norm_num : (0 : ℝ)<768)]
        ring
      rw [he]

theorem spectralKFramePhysicalTest_mass_le (ψ χ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hχ : ContDiff ℝ ∞ χ)
    (hSupp : tsupport ψ ⊆ Icc (Real.log 2) (Real.log 384))
    (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1) (hχ1 : ∀ u, |χ u| ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ, (spectralKFramePhysicalTest ψ χ T x)^2 ∂spectralKLPhysicalMeasure) ≤
      spectralKFrameLength := by
  let F := spectralKFramePhysicalTest ψ χ T
  let L := spectralKFrameLength
  have hL : 0 < L := spectralKFrameLength_pos
  have hz (x : ℝ) (hx : x ∉ Ioc (T/32) (24*T)) : (F x)^2 = 0 := by
    have he : F x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (spectralKFramePhysicalTest_log_support ψ χ hSupp T hT h))
    rw [he,zero_pow (by norm_num : (2:ℕ)≠0)]
  rw [spectralKFrame_integral_log (fun x => (F x)^2) T hT hz]
  simp_rw [F,spectralKFramePhysicalTest_scaledExp ψ χ T hT]
  calc
    _ ≤ ∫ u in (0 : ℝ)..L, (1 : ℝ) := by
      apply intervalIntegral.integral_mono_on hL.le
        (((hψ.mul hχ).continuous.pow 2).intervalIntegrable 0 L) intervalIntegrable_const
      intro u _
      change (ψ u*χ u)^2 ≤ 1
      have h := pow_le_pow_left₀ (abs_nonneg (ψ u*χ u))
        (show |ψ u*χ u| ≤ 1 by
          rw [abs_mul,abs_of_nonneg (h01 u).1]
          exact (mul_le_mul (h01 u).2 (hχ1 u) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)) 2
      simpa only [sq_abs,one_pow] using h
    _ = _ := by simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one,L]

end ArtinMatthews
