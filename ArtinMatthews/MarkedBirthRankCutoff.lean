module

public import ArtinMatthews.MarkedBirthAddressBudget


set_option backward.privateInPublic true
@[expose] public section

/-! The manuscript rank cutoff at the literal growing moment length.
Its relative size tends to zero for every fixed auxiliary constant; no
stronger band-depth or admissibility assumption is introduced. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped Topology

def markedBirthRankCutoff (cutoffScale x : ℝ) : ℕ :=
  ⌈cutoffScale*(markedMemoryMomentLength x:ℝ)*Real.log (Real.log x)/(Real.log x)^(1/10:ℝ)⌉₊

theorem markedMemoryMomentLength_lower {x : ℝ} (_hx : 0 ≤ Real.log x) :
    (Real.log x)^(1/2:ℝ) ≤ (markedMemoryMomentLength x:ℝ) := by
  have h := Nat.le_ceil ((Real.log x)^(1/2:ℝ)/2)
  unfold markedMemoryMomentLength
  push_cast
  linarith

theorem markedBirthRankCutoff_ratio_tendsto {cutoffScale : ℝ} (hcutoffScale : 0 ≤ cutoffScale) :
    Tendsto (fun x : ℝ => (markedBirthRankCutoff cutoffScale x:ℝ)/(markedMemoryMomentLength x:ℝ))
      atTop (𝓝 0) := by
  have ht₁ := (((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ)<1/10)).tendsto_div_nhds_zero).const_mul cutoffScale).comp
    Real.tendsto_log_atTop
  have ht₂ := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp Real.tendsto_log_atTop
  have ht := ht₁.add ht₂
  simp only [mul_zero,zero_add] at ht
  apply squeeze_zero' ?_ ?_ ht
  · exact Filter.Eventually.of_forall (fun x => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hlog
    have hL : 0 < Real.log x := zero_lt_one.trans_le hlog
    have hs : 0 < (Real.log x)^(1/2:ℝ) := Real.rpow_pos_of_pos hL _
    have ha : 0 < (Real.log x)^(1/10:ℝ) := Real.rpow_pos_of_pos hL _
    have hN := markedMemoryMomentLength_lower hL.le
    have hNp : 0 < (markedMemoryMomentLength x:ℝ) := hs.trans_le hN
    have hnum : 0 ≤ cutoffScale*(markedMemoryMomentLength x:ℝ)*Real.log (Real.log x)/(Real.log x)^(1/10:ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg hcutoffScale (Nat.cast_nonneg _)) (Real.log_nonneg hlog)) ha.le
    have hc := (Nat.ceil_lt_add_one hnum).le
    calc
      _ ≤ (cutoffScale*(markedMemoryMomentLength x:ℝ)*Real.log (Real.log x)/(Real.log x)^(1/10:ℝ)+1)/
          (markedMemoryMomentLength x:ℝ) := div_le_div_of_nonneg_right hc hNp.le
      _ = cutoffScale*(Real.log (Real.log x)/(Real.log x)^(1/10:ℝ)) + 1/(markedMemoryMomentLength x:ℝ) := by
        field_simp
      _ ≤ cutoffScale*(Real.log (Real.log x)/(Real.log x)^(1/10:ℝ)) + (Real.log x)^(-(1/2:ℝ)) := by
        apply add_le_add le_rfl
        rw [Real.rpow_neg hL.le,one_div]
        exact (inv_le_inv₀ hNp hs).mpr hN

theorem markedBirthRankCutoff_le_fraction {cutoffScale η : ℝ} (hcutoffScale : 0 ≤ cutoffScale) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop,
      (markedBirthRankCutoff cutoffScale x:ℝ) ≤ η*(markedMemoryMomentLength x:ℝ) := by
  filter_upwards [(markedBirthRankCutoff_ratio_tendsto hcutoffScale).eventually (Iio_mem_nhds hη),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  have hs : 0 < (Real.log x)^(1/2:ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _
  have hN : 0 < (markedMemoryMomentLength x:ℝ) :=
    hs.trans_le (markedMemoryMomentLength_lower (zero_le_one.trans hlog))
  exact ((div_lt_iff₀ hN).mp hx).le

end ArtinMatthews
