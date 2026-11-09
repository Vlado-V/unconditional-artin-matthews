module

public import ArtinMatthews.MarkedRootRatioCells
public import ArtinMatthews.MarkedRootArcIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! Exact lifted elementary circle arcs on a bounded real ratio range.
The finite endpoints are transported by the genuine Möbius map. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedRootLiftedArcRadius (q : ℤ) (R : ℝ) : ℕ := ⌈(q.natAbs:ℝ)*R+1⌉₊

def markedRootLiftedArcWindow (q : ℤ) (R : ℝ) : Finset ℤ :=
  Finset.Icc (-(markedRootLiftedArcRadius q R:ℤ)) (markedRootLiftedArcRadius q R:ℤ)

def markedRootLiftedArcLevels (q : ℤ) (R ε : ℝ) : Finset ℝ :=
  if q=0 then ∅ else
    (markedRootLiftedArcWindow q R).image (fun k : ℤ => ((k:ℝ)-ε)/(q.natAbs:ℝ)) ∪
      (markedRootLiftedArcWindow q R).image (fun k : ℤ => ((k:ℝ)+ε)/(q.natAbs:ℝ))

theorem markedRootLiftedArcWindow_card (q : ℤ) (R : ℝ) :
    (markedRootLiftedArcWindow q R).card = 2*markedRootLiftedArcRadius q R+1 := by
  simp only [markedRootLiftedArcWindow,Int.card_Icc]
  omega

theorem markedBadRootMultiple_lifted_cover (q : ℤ) (hq : q ≠ 0) {R ε y : ℝ}
    (_hR : 0 ≤ R) (hε : ε ≤ 1) (hy : |y| ≤ R) :
    (y:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε ↔
      ∃ k ∈ markedRootLiftedArcWindow q R,y ∈ markedRootArcInterval q.natAbs ε k := by
  rw [markedBadRootMultiple_natAbs]
  have hn : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  have hnorm : ‖(q.natAbs:ℤ) • (y:AddCircle (1:ℝ))‖ =
      |(q.natAbs:ℝ)*y-round ((q.natAbs:ℝ)*y)| := by
    have he : (q.natAbs:ℤ) • (y:AddCircle (1:ℝ)) =
        (((q.natAbs:ℝ)*y:ℝ):AddCircle (1:ℝ)) := by
      calc
        _ = (((q.natAbs:ℤ) • y:ℝ):AddCircle (1:ℝ)) := (AddCircle.coe_zsmul (1:ℝ)).symm
        _ = _ := by congr 1; simp only [zsmul_eq_mul,Int.cast_natCast]
    rw [he]
    simpa only [inv_one,one_mul,mul_one] using AddCircle.norm_eq (p := (1:ℝ)) (x := (q.natAbs:ℝ)*y)
  change ‖(q.natAbs:ℤ) • (y:AddCircle (1:ℝ))‖ ≤ ε ↔ _
  rw [hnorm]
  constructor
  · intro h
    refine ⟨round ((q.natAbs:ℝ)*y),?_,(markedRootArcInterval_iff hn ε y _).mpr h⟩
    have hp : |(q.natAbs:ℝ)*y| ≤ (q.natAbs:ℝ)*R := by
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg _)
    have hK : (q.natAbs:ℝ)*R+1 ≤ (markedRootLiftedArcRadius q R:ℝ) := Nat.le_ceil _
    apply Finset.mem_Icc.mpr
    constructor
    · apply (Int.cast_le (R := ℝ)).mp
      simp only [Int.cast_neg,Int.cast_natCast]
      linarith [(abs_le.mp h).1,(abs_le.mp h).2,(abs_le.mp hp).1,(abs_le.mp hp).2]
    · apply (Int.cast_le (R := ℝ)).mp
      simp only [Int.cast_natCast]
      linarith [(abs_le.mp h).1,(abs_le.mp h).2,(abs_le.mp hp).1,(abs_le.mp hp).2]
  · rintro ⟨k,_,hk⟩
    exact (round_le ((q.natAbs:ℝ)*y) k).trans ((markedRootArcInterval_iff hn ε y k).mp hk)

theorem markedRootLiftedArcLevels_card_le (q : ℤ) {R ε : ℝ} (hR : 0 ≤ R) :
    ((markedRootLiftedArcLevels q R ε).card:ℝ) ≤ 4*(q.natAbs:ℝ)*R+10 := by
  by_cases hq : q=0
  · simp only [markedRootLiftedArcLevels,ite_eq_left hq,Finset.card_empty,Nat.cast_zero]
    positivity
  · have hc : (markedRootLiftedArcLevels q R ε).card ≤ 2*(markedRootLiftedArcWindow q R).card := by
      rw [markedRootLiftedArcLevels,ite_eq_right hq]
      exact (Finset.card_union_le _ _).trans ((Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans_eq (by omega))
    have hcr : ((markedRootLiftedArcLevels q R ε).card:ℝ) ≤ 4*(markedRootLiftedArcRadius q R:ℝ)+2 := by
      rw [markedRootLiftedArcWindow_card] at hc
      have hh : ((markedRootLiftedArcLevels q R ε).card:ℝ) ≤ 2*(2*(markedRootLiftedArcRadius q R:ℝ)+1) := by
        exact_mod_cast hc
      linarith
    have hk := Nat.ceil_lt_add_one (show 0 ≤ (q.natAbs:ℝ)*R+1 by positivity)
    change (markedRootLiftedArcRadius q R:ℝ) < (q.natAbs:ℝ)*R+1+1 at hk
    linarith

theorem markedRootLiftedArcLevels_lower (q : ℤ) (hq : q ≠ 0) (R ε : ℝ) {k : ℤ}
    (hk : k ∈ markedRootLiftedArcWindow q R) :
    ((k:ℝ)-ε)/(q.natAbs:ℝ) ∈ markedRootLiftedArcLevels q R ε := by
  rw [markedRootLiftedArcLevels,ite_eq_right hq]
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,hk,rfl⟩)

theorem markedRootLiftedArcLevels_upper (q : ℤ) (hq : q ≠ 0) (R ε : ℝ) {k : ℤ}
    (hk : k ∈ markedRootLiftedArcWindow q R) :
    ((k:ℝ)+ε)/(q.natAbs:ℝ) ∈ markedRootLiftedArcLevels q R ε := by
  rw [markedRootLiftedArcLevels,ite_eq_right hq]
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,hk,rfl⟩)

theorem markedTransportedArc_iff_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (q : ℤ) {R ε r s : ℝ}
    (hR : 0 ≤ R) (hε : ε ≤ 1)
    (hr : |markedTransportedRatio r z w| ≤ R) (hs : |markedTransportedRatio s z w| ≤ R)
    (hcut : ∀ t ∈ Set.uIcc r s,t ∉ markedTransportedRatioAllCuts z w (markedRootLiftedArcLevels q R ε)) :
    ((markedTransportedRatio r z w:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε) ↔
      ((markedTransportedRatio s z w:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε) := by
  by_cases hq : q=0
  · simp only [hq,markedBadRootMultiple,Set.mem_ofPred_eq,zero_smul,norm_zero]
  · rw [markedBadRootMultiple_lifted_cover q hq hR hε hr,
      markedBadRootMultiple_lifted_cover q hq hR hε hs]
    have hi (k : ℤ) (hk : k ∈ markedRootLiftedArcWindow q R) :=
      markedTransportedRatio_interval_iff_off_cuts z w hdet (markedRootLiftedArcLevels q R ε)
        (markedRootLiftedArcLevels_lower q hq R ε hk) (markedRootLiftedArcLevels_upper q hq R ε hk) hcut
    constructor
    · rintro ⟨k,hk,hmem⟩
      exact ⟨k,hk,(hi k hk).mp hmem⟩
    · rintro ⟨k,hk,hmem⟩
      exact ⟨k,hk,(hi k hk).mpr hmem⟩

theorem markedTransportedRatio_constant_of_det_zero (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 0) {r s : ℝ}
    (hr : markedTau r z ≠ 0) (hs : markedTau s z ≠ 0) :
    markedTransportedRatio r z w = markedTransportedRatio s z w := by
  apply (div_eq_div_iff hr hs).mpr
  exact sub_eq_zero.mp (by simpa only [hdet,zero_mul] using markedTau_cross_difference r s z w)

theorem markedTransportedRatio_zero_source (w : Fin 2 → ℝ) (r : ℝ) :
    markedTransportedRatio r (fun _ => 0) w = 0 := by simp [markedTransportedRatio,markedTau]

end ArtinMatthews
