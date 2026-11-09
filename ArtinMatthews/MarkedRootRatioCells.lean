module

public import ArtinMatthews.MarkedRootRatioCutVolume
public import Mathlib.Topology.Order.IntermediateValue


set_option backward.privateInPublic true
@[expose] public section

/-! Actual transported ratio tests are constant between their explicit
Möbius level cuts and the one possible pole. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory

def markedTransportedRatioAllCuts (z w : Fin 2 → ℝ) (levels : Finset ℝ) : Finset ℝ :=
  insert (-z 0/z 1) (markedTransportedRatioCuts z w levels)

theorem markedTransportedRatioAllCuts_card_le (z w : Fin 2 → ℝ) (levels : Finset ℝ) :
    (markedTransportedRatioAllCuts z w levels).card ≤ levels.card+1 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (markedTransportedRatioCuts_card_le z w levels) 1)

theorem markedTau_ne_zero_off_ratio_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r : ℝ}
    (hr : r ∉ markedTransportedRatioAllCuts z w levels) : markedTau r z ≠ 0 := by
  intro hzero
  have hz1 : z 1 ≠ 0 := by
    intro hz
    have hz0 : z 0=0 := by simpa only [markedTau,hz,mul_zero,add_zero] using hzero
    simp only [markedVectorDet,hz,hz0,zero_mul,sub_zero] at hdet
    norm_num at hdet
  have he : r = -z 0/z 1 := (eq_div_iff hz1).mpr (by unfold markedTau at hzero; linarith)
  apply hr
  exact Finset.mem_insert.mpr (Or.inl he)

theorem markedTransportedRatio_ne_level_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r a : ℝ}
    (hr : r ∉ markedTransportedRatioAllCuts z w levels) (ha : a ∈ levels) :
    markedTransportedRatio r z w ≠ a := by
  intro he
  have hc := markedTransportedRatio_mem_cuts z w hdet levels
    (markedTau_ne_zero_off_ratio_cuts z w hdet levels hr) (he ▸ ha)
  exact hr (Finset.mem_insert_of_mem hc)

theorem markedTransportedRatio_le_iff_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r s a : ℝ}
    (ha : a ∈ levels)
    (hcut : ∀ t ∈ Set.uIcc r s,t ∉ markedTransportedRatioAllCuts z w levels) :
    markedTransportedRatio r z w ≤ a ↔ markedTransportedRatio s z w ≤ a := by
  have hτ : ∀ t ∈ Set.uIcc r s,markedTau t z ≠ 0 :=
    fun t ht => markedTau_ne_zero_off_ratio_cuts z w hdet levels (hcut t ht)
  have hz : Continuous (fun t => markedTau t z) := by unfold markedTau; fun_prop
  have hw : Continuous (fun t => markedTau t w) := by unfold markedTau; fun_prop
  have hf : ContinuousOn (fun t => markedTransportedRatio t z w) (Set.uIcc r s) :=
    hw.continuousOn.div hz.continuousOn hτ
  have hno : ∀ t ∈ Set.uIcc r s,markedTransportedRatio t z w ≠ a :=
    fun t ht => markedTransportedRatio_ne_level_off_cuts z w hdet levels (hcut t ht) ha
  constructor
  · intro hr
    by_contra hs
    have hab : a ∈ Set.uIcc (markedTransportedRatio r z w) (markedTransportedRatio s z w) :=
      Set.mem_uIcc.mpr (Or.inl ⟨hr,(lt_of_not_ge hs).le⟩)
    obtain ⟨t,ht,he⟩ := intermediate_value_uIcc hf hab
    exact hno t ht he
  · intro hs
    by_contra hr
    have hab : a ∈ Set.uIcc (markedTransportedRatio r z w) (markedTransportedRatio s z w) :=
      Set.mem_uIcc.mpr (Or.inr ⟨hs,(lt_of_not_ge hr).le⟩)
    obtain ⟨t,ht,he⟩ := intermediate_value_uIcc hf hab
    exact hno t ht he

theorem markedTransportedRatio_lt_iff_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r s a : ℝ}
    (ha : a ∈ levels)
    (hcut : ∀ t ∈ Set.uIcc r s,t ∉ markedTransportedRatioAllCuts z w levels) :
    markedTransportedRatio r z w < a ↔ markedTransportedRatio s z w < a := by
  have hr := markedTransportedRatio_ne_level_off_cuts z w hdet levels (hcut r Set.left_mem_uIcc) ha
  have hs := markedTransportedRatio_ne_level_off_cuts z w hdet levels (hcut s Set.right_mem_uIcc) ha
  rw [lt_iff_le_and_ne,lt_iff_le_and_ne]
  exact and_congr (markedTransportedRatio_le_iff_off_cuts z w hdet levels ha hcut) (iff_of_true hr hs)

theorem markedTransportedRatio_interval_iff_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r s a b : ℝ}
    (ha : a ∈ levels) (hb : b ∈ levels)
    (hcut : ∀ t ∈ Set.uIcc r s,t ∉ markedTransportedRatioAllCuts z w levels) :
    markedTransportedRatio r z w ∈ Set.Icc a b ↔ markedTransportedRatio s z w ∈ Set.Icc a b := by
  have hlo := not_congr (markedTransportedRatio_lt_iff_off_cuts z w hdet levels ha hcut)
  have hhi := markedTransportedRatio_le_iff_off_cuts z w hdet levels hb hcut
  simpa only [Set.mem_Icc,not_lt] using and_congr hlo hhi

theorem markedRootRatioAllCuts_grid_volume_le (z w : Fin 2 → ℝ) (levels : Finset ℝ)
    {h : ℝ} (hh : 0 ≤ h) :
    markedNormalizedRootMeasure
      (markedRootCutNeighborhood (markedTransportedRatioAllCuts z w levels) h ×ˢ (Set.univ : Set (ℝ × ℝ))) ≤
      ENNReal.ofReal (30*((levels.card:ℝ)+1)*h) := by
  unfold markedNormalizedRootMeasure
  rw [Measure.prod_prod]
  have hmass : ((volume.restrict (Set.Icc (1:ℝ) 16)).prod
      (volume.restrict (Set.Icc (1:ℝ) 2))) Set.univ = 15 := by
    rw [← Set.univ_prod_univ,Measure.prod_prod]
    simp only [Measure.restrict_apply_univ,Real.volume_Icc]
    norm_num
  rw [hmass]
  calc
    _ ≤ volume (markedRootCutNeighborhood (markedTransportedRatioAllCuts z w levels) h)*15 :=
      mul_le_mul' (Measure.restrict_apply_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (2*((markedTransportedRatioAllCuts z w levels).card:ℝ)*h)*15 :=
      mul_le_mul' (markedRootCutNeighborhood_volume_le _ hh) le_rfl
    _ ≤ ENNReal.ofReal (2*((levels.card:ℝ)+1)*h)*15 := by
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      have hc : ((markedTransportedRatioAllCuts z w levels).card:ℝ) ≤ (levels.card:ℝ)+1 := by
        exact_mod_cast markedTransportedRatioAllCuts_card_le z w levels
      nlinarith
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*((levels.card:ℝ)+1)*h)]
      congr 1
      ring

end ArtinMatthews
