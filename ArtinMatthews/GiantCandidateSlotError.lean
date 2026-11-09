module

public import ArtinMatthews.GiantCandidatePrimeStrip


set_option backward.privateInPublic true
@[expose] public section

/-! One-slot positive envelopes and the three contributions to the
literal rough-proxy replacement. -/

namespace ArtinMatthews
noncomputable section

def GiantCandidateProxySupport (W z : ℝ) (m : ℕ) : Prop :=
  z < (m:ℝ) ∧ ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m

instance (W z : ℝ) (m : ℕ) : Decidable (GiantCandidateProxySupport W z m) :=
  inferInstanceAs (Decidable (z < (m:ℝ) ∧ ∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m))

def giantCandidateSlotBound (W z : ℝ) : ℝ :=
  (markedSieveEulerProduct W)⁻¹ / Real.log z

def giantCandidateProxyEnvelope (W z : ℝ) (m : ℕ) : ℝ :=
  if GiantCandidateProxySupport W z m then giantCandidateSlotBound W z else 0

theorem giantCandidateSlotBound_nonneg {W z : ℝ} (hz : 1 < z) :
    0 ≤ giantCandidateSlotBound W z :=
  div_nonneg (inv_nonneg.mpr (markedSieveEulerProduct_pos W).le) (Real.log_pos hz).le

theorem giantCandidateProxyEnvelope_nonneg {W z : ℝ} (hz : 1 < z) (m : ℕ) :
    0 ≤ giantCandidateProxyEnvelope W z m := by
  unfold giantCandidateProxyEnvelope
  split_ifs
  · exact giantCandidateSlotBound_nonneg hz
  · exact le_rfl

theorem giantRoughSlotCoefficient_eq_zero_of_not_support (W z : ℝ) (m : ℕ)
    (hm : ¬GiantCandidateProxySupport W z m) :
    giantRoughSlotCoefficient W z m = 0 := by
  by_cases hzm : z < (m:ℝ)
  · have hr : ¬∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m := fun h => hm ⟨hzm,h⟩
    simp only [giantRoughSlotCoefficient,ite_eq_left hzm,ite_eq_right hr,mul_zero]
  · exact ite_eq_right hzm

theorem giantCandidateStrippedSlotCoefficient_eq_zero_of_not_support (P : Finset ℕ)
    (W z : ℝ) (m : ℕ) (hm : ¬GiantCandidateProxySupport W z m) :
    giantCandidateStrippedSlotCoefficient P W z m = 0 := by
  by_cases hzm : z < (giantCandidateStrip P m:ℝ)
  · have hzm' := hzm.trans_le (Nat.cast_le.mpr (giantCandidateStrip_le P m))
    have hr : ¬∀ p ∈ Nat.primesLE ⌊W⌋₊, ¬p ∣ m := fun h => hm ⟨hzm',h⟩
    simp only [giantCandidateStrippedSlotCoefficient,ite_eq_left hzm,ite_eq_right hr,mul_zero]
  · exact ite_eq_right hzm

private theorem giantCandidateReciprocal_norm_le {W z t : ℝ} (hz : 1 < z)
    (ht : z < t) :
    ‖(markedSieveEulerProduct W:ℂ)⁻¹*((Real.log t)⁻¹:ℝ)‖ ≤ giantCandidateSlotBound W z := by
  have hV := markedSieveEulerProduct_pos W
  have hlogz := Real.log_pos hz
  have hlogt := Real.log_pos (hz.trans ht)
  have hle := Real.log_le_log (zero_lt_one.trans hz) ht.le
  rw [giantCandidateSlotBound,norm_mul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hV,abs_of_pos (inv_pos.mpr hlogt),div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hlogt hlogz).mpr hle) (inv_nonneg.mpr hV.le)

theorem giantRoughSlotCoefficient_norm_le_envelope {W z : ℝ} (hz : 1 < z) (m : ℕ) :
    ‖giantRoughSlotCoefficient W z m‖ ≤ giantCandidateProxyEnvelope W z m := by
  by_cases hm : GiantCandidateProxySupport W z m
  · rw [giantCandidateProxyEnvelope,ite_eq_left hm]
    unfold giantRoughSlotCoefficient
    rw [ite_eq_left hm.1,ite_eq_left hm.2,mul_one]
    exact giantCandidateReciprocal_norm_le hz hm.1
  · rw [giantRoughSlotCoefficient_eq_zero_of_not_support W z m hm,
      giantCandidateProxyEnvelope,ite_eq_right hm,norm_zero]

theorem giantCandidateStrippedSlotCoefficient_norm_le_envelope (P : Finset ℕ)
    {W z : ℝ} (hz : 1 < z) (m : ℕ) :
    ‖giantCandidateStrippedSlotCoefficient P W z m‖ ≤ giantCandidateProxyEnvelope W z m := by
  by_cases hm : GiantCandidateProxySupport W z m
  · rw [giantCandidateProxyEnvelope,ite_eq_left hm]
    unfold giantCandidateStrippedSlotCoefficient
    by_cases hzm : z < (giantCandidateStrip P m:ℝ)
    · rw [ite_eq_left hzm,ite_eq_left hm.2,mul_one]
      exact giantCandidateReciprocal_norm_le hz hzm
    · rw [ite_eq_right hzm,norm_zero]
      exact giantCandidateSlotBound_nonneg hz
  · rw [giantCandidateStrippedSlotCoefficient_eq_zero_of_not_support P W z m hm,
      giantCandidateProxyEnvelope,ite_eq_right hm,norm_zero]

private theorem giantCandidateSlotError_small (P : Finset ℕ) {W z R : ℝ}
    {m : ℕ} (hz : 1 < z) (hs : GiantCandidateProxySupport W z m)
    (hR : 0 ≤ R) (hr : giantCandidateRemovedLog P m ≤ R)
    (hstrip : Real.log z + R < Real.log (m:ℝ)) :
    ‖giantRoughSlotCoefficient W z m - giantCandidateStrippedSlotCoefficient P W z m‖ ≤
      giantCandidateSlotBound W z * R / Real.log z := by
  have hmR : (0:ℝ) < m := (zero_lt_one.trans hz).trans hs.1
  have hm : 0 < m := Nat.cast_pos.mp hmR
  have hsm : (0:ℝ) < giantCandidateStrip P m := Nat.cast_pos.mpr (giantCandidateStrip_pos P hm)
  have he := giantCandidateRemovedLog_eq_sub P hm
  have hstr : z < (giantCandidateStrip P m:ℝ) := by
    by_contra h
    have hh := Real.log_le_log hsm (le_of_not_gt h)
    linarith only [hh,he,hstrip,hr]
  let a := Real.log (m:ℝ)
  let b := Real.log (giantCandidateStrip P m:ℝ)
  let c := Real.log z
  let V := markedSieveEulerProduct W
  have hc : 0 < c := Real.log_pos hz
  have ha : c ≤ a := Real.log_le_log (zero_lt_one.trans hz) hs.1.le
  have hb : c ≤ b := Real.log_le_log (zero_lt_one.trans hz) hstr.le
  have ha₀ : 0 < a := hc.trans_le ha
  have hb₀ : 0 < b := hc.trans_le hb
  have hV : 0 < V := markedSieveEulerProduct_pos W
  have hinv : a⁻¹-b⁻¹ = -(giantCandidateRemovedLog P m/(a*b)) := by
    change giantCandidateRemovedLog P m = a-b at he
    rw [he]
    field_simp [ha₀.ne',hb₀.ne']
    ring
  have hab : c*c ≤ a*b := mul_le_mul ha hb hc.le ha₀.le
  have hn : 0 ≤ giantCandidateRemovedLog P m/(a*b) :=
    div_nonneg (giantCandidateRemovedLog_nonneg P m) (mul_pos ha₀ hb₀).le
  unfold giantRoughSlotCoefficient giantCandidateStrippedSlotCoefficient
  rw [ite_eq_left hs.1,ite_eq_left hstr,ite_eq_left hs.2,mul_one,mul_one,← mul_sub]
  change ‖(V:ℂ)⁻¹ * ((a⁻¹:ℝ)-(b⁻¹:ℝ):ℂ)‖ ≤ giantCandidateSlotBound W z * R / c
  rw [← Complex.ofReal_sub,hinv,norm_mul,norm_inv,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hV,abs_neg,abs_of_nonneg hn]
  calc
    _ ≤ V⁻¹*(R/(a*b)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right hr (mul_pos ha₀ hb₀).le) (inv_nonneg.mpr hV.le)
    _ ≤ V⁻¹*(R/(c*c)) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hR (mul_pos hc hc) hab) (inv_nonneg.mpr hV.le)
    _ = _ := by
      change V⁻¹*(R/(c*c)) = (V⁻¹/c)*R/c
      rw [div_mul_eq_div_div]
      ring

theorem giantCandidateSlotError_le (P : Finset ℕ) {W z R : ℝ} {m : ℕ}
    (hz : 1 < z) (hR : 0 ≤ R) (hs : GiantCandidateProxySupport W z m) :
    ‖giantRoughSlotCoefficient W z m - giantCandidateStrippedSlotCoefficient P W z m‖ ≤
      2*giantCandidateSlotBound W z*(if R < giantCandidateRemovedLog P m then 1 else 0) +
      2*giantCandidateSlotBound W z*(if Real.log (m:ℝ) ≤ Real.log z+R then 1 else 0) +
      giantCandidateSlotBound W z*R/Real.log z := by
  let A := giantCandidateSlotBound W z
  have hA : 0 ≤ A := giantCandidateSlotBound_nonneg hz
  have he : giantCandidateProxyEnvelope W z m = A := ite_eq_left hs
  have htr := norm_sub_le (giantRoughSlotCoefficient W z m) (giantCandidateStrippedSlotCoefficient P W z m)
  have h₂ : ‖giantRoughSlotCoefficient W z m - giantCandidateStrippedSlotCoefficient P W z m‖ ≤ 2*A := by
    apply htr.trans
    have h₁ := giantRoughSlotCoefficient_norm_le_envelope (W:=W) hz m
    have h₂ := giantCandidateStrippedSlotCoefficient_norm_le_envelope P (W:=W) hz m
    rw [he] at h₁ h₂
    linarith only [h₁,h₂]
  have hlast : 0 ≤ A*R/Real.log z := div_nonneg (mul_nonneg hA hR) (Real.log_pos hz).le
  change _ ≤ 2*A*(if R < giantCandidateRemovedLog P m then 1 else 0) +
      2*A*(if Real.log (m:ℝ) ≤ Real.log z+R then 1 else 0) + A*R/Real.log z
  by_cases hbad : R < giantCandidateRemovedLog P m
  · rw [ite_eq_left hbad,mul_one]
    have htest : 0 ≤ (if Real.log (m:ℝ) ≤ Real.log z+R then (1:ℝ) else 0) := by
      split_ifs <;> norm_num
    exact h₂.trans (by linarith only [hlast,mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hA) htest])
  · rw [ite_eq_right hbad,mul_zero,zero_add]
    by_cases hstrip : Real.log (m:ℝ) ≤ Real.log z+R
    · rw [ite_eq_left hstrip,mul_one]
      exact h₂.trans (by linarith only [hlast])
    · rw [ite_eq_right hstrip,mul_zero,zero_add]
      exact giantCandidateSlotError_small P hz hs hR (le_of_not_gt hbad) (lt_of_not_ge hstrip)

end
end ArtinMatthews
