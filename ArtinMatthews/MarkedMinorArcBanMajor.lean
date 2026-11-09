module

public import ArtinMatthews.MarkedMinorArcCircle
public import Mathlib.MeasureTheory.Group.AddCircle


set_option backward.privateInPublic true
@[expose] public section

/-! The actual rational-major-arc measure and its ordinary Fourier kernel. -/
noncomputable section
namespace ArtinMatthews

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩

theorem markedBan_integer_circle_zero (k : ℤ) : ((k:ℝ):AddCircle (1:ℝ)) = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  have hh := AddSubgroup.zsmul_mem_zmultiples (1:ℝ) k
  simpa only [zsmul_eq_mul,mul_one] using hh

theorem markedBan_rat_circle_remainder (r : ℚ) :
    ((r:ℝ):AddCircle (1:ℝ)) =
      ((((r.num % (r.den:ℤ):ℤ):ℝ)/(r.den:ℝ):ℝ):AddCircle (1:ℝ)) := by
  have hd : (r.den:ℝ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hc := congrArg (fun z : ℤ => (z:ℝ)) (Int.emod_add_mul_ediv r.num (r.den:ℤ))
  simp only [Int.cast_add,Int.cast_mul,Int.cast_natCast] at hc
  have he : (r:ℝ) = ((r.num % (r.den:ℤ):ℤ):ℝ)/(r.den:ℝ)+
      ((r.num / (r.den:ℤ):ℤ):ℝ) := by
    rw [Rat.cast_def]
    field_simp [hd]
    nlinarith [hc]
  rw [he,AddCircle.coe_add,markedBan_integer_circle_zero,add_zero]

theorem markedBan_major_cover {Q Y : ℝ} (hQ : 0 ≤ Q) :
    markedMinorCircleMajor Q Y ⊆
      ⋃ d ∈ Finset.Icc 1 ⌊Q⌋₊, ⋃ a ∈ Finset.range ⌊Q⌋₊,
        closedBall ((((a:ℝ)/(d:ℝ):ℝ):AddCircle (1:ℝ))) (2*Q/Y) := by
  intro θ hθ
  obtain ⟨r,hr⟩ := mem_iUnion.mp hθ
  split_ifs at hr with hden
  · have hd : r.den ≤ ⌊Q⌋₊ := (Nat.le_floor_iff hQ).mpr hden
    have hdpos : (0:ℤ) < r.den := by exact_mod_cast r.den_pos
    have hr0 := Int.emod_nonneg r.num (by exact_mod_cast r.den_ne_zero : (r.den:ℤ)≠0)
    have hrlt := Int.emod_lt_of_pos r.num hdpos
    let a : ℕ := (r.num % (r.den:ℤ)).toNat
    have haeq : (a:ℤ) = r.num % (r.den:ℤ) := Int.toNat_of_nonneg hr0
    have ha : a < ⌊Q⌋₊ := by omega
    apply mem_iUnion₂.mpr
    refine ⟨r.den,Finset.mem_Icc.mpr ⟨r.den_pos,hd⟩,mem_iUnion₂.mpr ⟨a,Finset.mem_range.mpr ha,?_⟩⟩
    have hcenter : ((r:ℝ):AddCircle (1:ℝ)) = (((a:ℝ)/(r.den:ℝ):ℝ):AddCircle (1:ℝ)) := by
      rw [markedBan_rat_circle_remainder]
      congr 2
      exact_mod_cast haeq.symm
    rwa [hcenter] at hr
  · exact False.elim hr

theorem markedBan_major_measure_le {Q Y : ℝ} (hQ : 0 ≤ Q) :
    volume (markedMinorCircleMajor Q Y) ≤
      (⌊Q⌋₊:ℝ≥0∞)^2*ENNReal.ofReal (4*Q/Y) := by
  have hball (d a : ℕ) : volume (closedBall ((((a:ℝ)/(d:ℝ):ℝ):AddCircle (1:ℝ))) (2*Q/Y)) ≤
      ENNReal.ofReal (4*Q/Y) := by
    rw [AddCircle.volume_closedBall]
    apply ENNReal.ofReal_le_ofReal
    exact (min_le_right _ _).trans_eq (by ring)
  apply (measure_mono (markedBan_major_cover hQ)).trans
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ a ∈ Finset.range ⌊Q⌋₊, ENNReal.ofReal (4*Q/Y) := by
      apply Finset.sum_le_sum
      intro d _
      exact (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun a _ => hball d a))
    _ = _ := by simp [pow_two,mul_assoc]

theorem markedBan_major_real_measure_le {Q Y : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y) :
    volume.real (markedMinorCircleMajor Q Y) ≤ 4*Q^3/Y := by
  have hh := ENNReal.toReal_mono (by finiteness :
    (⌊Q⌋₊:ℝ≥0∞)^2*ENNReal.ofReal (4*Q/Y) ≠ ⊤) (markedBan_major_measure_le (Y := Y) hQ)
  have hr : volume.real (markedMinorCircleMajor Q Y) ≤ (⌊Q⌋₊:ℝ)^2*(4*Q/Y) := by
    simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Q/Y)] using hh
  calc
    _ ≤ (⌊Q⌋₊:ℝ)^2*(4*Q/Y) := hr
    _ ≤ Q^2*(4*Q/Y) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hQ) 2) (by positivity)
    _ = _ := by ring

def markedBanMajorKernel (Q Y : ℝ) (k : ℤ) : ℂ :=
  ∫ θ : AddCircle (1:ℝ) in markedMinorCircleMajor Q Y, fourier k θ ∂AddCircle.haarAddCircle

theorem markedBanMajorKernel_norm_le {Q Y : ℝ} (hQ : 0 ≤ Q) (hY : 0 < Y) (k : ℤ) :
    ‖markedBanMajorKernel Q Y k‖ ≤ 4*Q^3/Y := by
  have hv : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
    simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  have hn : ‖markedBanMajorKernel Q Y k‖ ≤ AddCircle.haarAddCircle.real (markedMinorCircleMajor Q Y) := by
    have hh := norm_setIntegral_le_of_norm_le_const
      (by finiteness : AddCircle.haarAddCircle (markedMinorCircleMajor Q Y) < ⊤)
      (fun θ (_ : θ ∈ markedMinorCircleMajor Q Y) =>
        by simp only [fourier_apply,Circle.norm_coe,le_refl] :
          ∀ θ ∈ markedMinorCircleMajor Q Y, ‖fourier k θ‖ ≤ (1:ℝ))
    simpa only [markedBanMajorKernel,one_mul] using hh
  rw [← hv] at hn
  exact hn.trans (markedBan_major_real_measure_le hQ hY)

end ArtinMatthews
