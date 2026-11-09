module

public import ArtinMatthews.GiantSignedJoinedSourceFamily
public import ArtinMatthews.GiantCandidateSelectedGroups
public import ArtinMatthews.IdealPrimeCellInterval


set_option backward.privateInPublic true
@[expose] public section

/-! The actual selected candidate groups supply the source band
conditions. The full selection supplies both lower group counts. -/
namespace ArtinMatthews
open Filter
noncomputable section

def giantCandidatePerformedLowerRate : ℝ := (5/100)/(2*Real.log 2)

theorem giantCandidatePrimeInterval_ideal (Y : ℝ) : IdealPrimeInterval (giantCandidatePrimeInterval Y) := by
  intro a ha b hb p hp hpa hpb
  obtain ⟨_,ha',_⟩ := mem_giantCandidatePrimeInterval.mp ha
  obtain ⟨_,_,hb'⟩ := mem_giantCandidatePrimeInterval.mp hb
  exact mem_giantCandidatePrimeInterval.mpr ⟨hp, ha'.trans (Nat.cast_le.mpr hpa),
    (Nat.cast_le.mpr hpb).trans_lt hb'⟩

theorem giantCandidatePerformedGeometry_eventually :
    ∀ᶠ x : ℝ in atTop, ∀ groups : Finset (GiantCandidateGroupIndex x),
      let PS := giantCandidatePerformedSmallBand groups
      let PB := giantCandidatePerformedBigBand groups
      let L := Real.log x
      (∀ j p, p ∈ PS j → p.Prime) ∧ (∀ j p, p ∈ PB j → p.Prime) ∧
      Pairwise (fun i j => Disjoint (PS i) (PS j)) ∧
      Pairwise (fun i j => Disjoint (PB i) (PB j)) ∧
      (∀ i j, Disjoint (PS i) (PB j)) ∧
      (∀ j, Real.log 2/2 ≤ bandReciprocalMass (PS j)) ∧
      (∀ j, Real.log 2/2 ≤ bandReciprocalMass (PB j)) ∧
      (∀ j, bandReciprocalMass (PB j) ≤ 1) ∧
      (∀ j, IdealPrimeInterval (PB j)) ∧
      (∀ j p, p ∈ PS j → (p : ℝ) ≤ Real.exp (L^(35/100 : ℝ))) ∧
      (∀ j p, p ∈ PB j → Real.exp (L^(40/100 : ℝ)) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp (L^(45/100 : ℝ))) ∧
      (Fintype.card (GiantCandidatePerformedSmall groups) : ℝ) ≤ giantCandidateGroupLogRate*Real.log L ∧
      (Fintype.card (GiantCandidatePerformedBig groups) : ℝ) ≤ giantCandidateGroupLogRate*Real.log L := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    giantCandidateGroup_mass_eventually, giantCandidateGroup_total_count_eventually] with x hx hL hMass hCount
  intro groups
  let S := GiantCandidatePerformedSmall groups
  let B := GiantCandidatePerformedBig groups
  let PS := giantCandidatePerformedSmallBand groups
  let PB := giantCandidatePerformedBigBand groups
  have hsmall (i : S) (p : ℕ) (hp : p ∈ PS i) := giantCandidateSmallGroup_range hx hL hp
  have hbig (j : B) (p : ℕ) (hp : p ∈ PB j) := giantCandidateBigGroup_range hx hL hp
  have hd := giantCandidateGroup_pairwise_disjoint hx hL
  have hS : Fintype.card S ≤ Fintype.card (GiantCandidateGroupIndex x) :=
    Fintype.card_le_of_injective (fun i : S => (Sum.inl i.val : GiantCandidateGroupIndex x))
      (Sum.inl_injective.comp Subtype.val_injective)
  have hB : Fintype.card B ≤ Fintype.card (GiantCandidateGroupIndex x) :=
    Fintype.card_le_of_injective (fun i : B => (Sum.inr i.val : GiantCandidateGroupIndex x))
      (Sum.inr_injective.comp Subtype.val_injective)
  refine ⟨fun i p hp => (hsmall i p hp).1, fun j p hp => (hbig j p hp).1,
    ?_, ?_, ?_, fun i => (hMass (.inl i.val)).1.le, fun j => (hMass (.inr j.val)).1.le,
    fun j => (hMass (.inr j.val)).2.le, fun j => giantCandidatePrimeInterval_ideal _,
    fun i p hp => (hsmall i p hp).2.2.le,
    fun j p hp => ⟨(hbig j p hp).2.1,(hbig j p hp).2.2.le⟩,
    (Nat.cast_le.mpr hS).trans hCount, (Nat.cast_le.mpr hB).trans hCount⟩
  · intro i j hij
    exact hd (fun h => hij (Subtype.ext (Sum.inl_injective h)))
  · intro i j hij
    exact hd (fun h => hij (Subtype.ext (Sum.inr_injective h)))
  · intro i j
    exact hd Sum.inl_ne_inr

theorem giantCandidatePerformedUniv_lower_eventually :
    ∀ᶠ x : ℝ in atTop,
      let groups : Finset (GiantCandidateGroupIndex x) := Finset.univ
      giantCandidatePerformedLowerRate * Real.log (Real.log x) ≤
        (Fintype.card (GiantCandidatePerformedSmall groups) : ℝ) ∧
      giantCandidatePerformedLowerRate * Real.log (Real.log x) ≤
        (Fintype.card (GiantCandidatePerformedBig groups) : ℝ) := by
  filter_upwards [giantCandidateGroup_counts_eventually,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx hL
  dsimp only
  rw [Fintype.card_congr (giantCandidatePerformedSmallUnivEquiv x),
    Fintype.card_congr (giantCandidatePerformedBigUnivEquiv x)]
  have hlog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hc : giantCandidatePerformedLowerRate ≤ (35/100-28/100)/(2*Real.log 2) := by
    unfold giantCandidatePerformedLowerRate
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  refine ⟨(mul_le_mul_of_nonneg_right hc hlog).trans hx.1,?_⟩
  simpa only [giantCandidatePerformedLowerRate, show (45/100-40/100 : ℝ) = 5/100 by norm_num] using hx.2.2.1

end
end ArtinMatthews
