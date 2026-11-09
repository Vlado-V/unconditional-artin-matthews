module

public import ArtinMatthews.GiantCandidateBandMass


set_option backward.privateInPublic true
@[expose] public section

/-! The literal small and big candidate groups of the composite argument.
Each group is a full half-open prime interval. The count and mass
conditions hold uniformly as the index types grow. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section

abbrev GiantCandidateSmallGroupIndex (x : ℝ) :=
  Fin (giantCandidateGroupCount (28/100) (35/100) x)

abbrev GiantCandidateBigGroupIndex (x : ℝ) :=
  Fin (giantCandidateGroupCount (40/100) (45/100) x)

abbrev GiantCandidateGroupIndex (x : ℝ) :=
  GiantCandidateSmallGroupIndex x ⊕ GiantCandidateBigGroupIndex x

def giantCandidateSmallGroup (x : ℝ) (i : GiantCandidateSmallGroupIndex x) : Finset ℕ :=
  giantCandidatePrimeInterval (giantCandidateGroupHeight (28/100) x i.val)

def giantCandidateBigGroup (x : ℝ) (i : GiantCandidateBigGroupIndex x) : Finset ℕ :=
  giantCandidatePrimeInterval (giantCandidateGroupHeight (40/100) x i.val)

def giantCandidateGroup (x : ℝ) : GiantCandidateGroupIndex x → Finset ℕ :=
  Sum.elim (giantCandidateSmallGroup x) (giantCandidateBigGroup x)

def giantCandidateFullPrimes (x : ℝ) : Finset ℕ :=
  univ.biUnion (giantCandidateGroup x)

theorem mem_giantCandidateFullPrimes {x : ℝ} {p : ℕ} :
    p ∈ giantCandidateFullPrimes x ↔ ∃ i : GiantCandidateGroupIndex x, p ∈ giantCandidateGroup x i := by
  simp only [giantCandidateFullPrimes,mem_biUnion,mem_univ,true_and]

theorem mem_giantCandidateBigGroup {x : ℝ} {i : GiantCandidateBigGroupIndex x} {p : ℕ} :
    p ∈ giantCandidateBigGroup x i ↔
      p.Prime ∧ Real.exp (giantCandidateGroupHeight (40/100) x i.val) ≤ (p:ℝ) ∧
        (p:ℝ) < Real.exp (2*giantCandidateGroupHeight (40/100) x i.val) :=
  mem_giantCandidatePrimeInterval

private theorem giantCandidate_group_range {a b x : ℝ} (hab : a ≤ b) (hx : 1 < x)
    (hlog : 1 ≤ Real.log x) {k p : ℕ} (hk : k < giantCandidateGroupCount a b x)
    (hp : p ∈ giantCandidatePrimeInterval (giantCandidateGroupHeight a x k)) :
    p.Prime ∧ Real.exp ((Real.log x)^a) ≤ (p:ℝ) ∧ (p:ℝ) < Real.exp ((Real.log x)^b) := by
  obtain ⟨hprime,hlo,hhi⟩ := mem_giantCandidatePrimeInterval.mp hp
  exact ⟨hprime,(Real.exp_le_exp.mpr (giantCandidateGroupHeight_ge a x hx k)).trans hlo,
    hhi.trans_le (Real.exp_le_exp.mpr ((giantCandidateGroupIndex_iff hab hlog k).mp hk))⟩

theorem giantCandidateSmallGroup_range {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    {i : GiantCandidateSmallGroupIndex x} {p : ℕ} (hp : p ∈ giantCandidateSmallGroup x i) :
    p.Prime ∧ Real.exp ((Real.log x)^(28/100:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) < Real.exp ((Real.log x)^(35/100:ℝ)) :=
  giantCandidate_group_range (by norm_num) hx hlog i.isLt hp

theorem giantCandidateBigGroup_range {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    {i : GiantCandidateBigGroupIndex x} {p : ℕ} (hp : p ∈ giantCandidateBigGroup x i) :
    p.Prime ∧ Real.exp ((Real.log x)^(40/100:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) < Real.exp ((Real.log x)^(45/100:ℝ)) :=
  giantCandidate_group_range (by norm_num) hx hlog i.isLt hp

private theorem giantCandidate_same_family_disjoint (a b x : ℝ) (hx : 1 < x) :
    Pairwise (fun i j : Fin (giantCandidateGroupCount a b x) =>
      Disjoint (giantCandidatePrimeInterval (giantCandidateGroupHeight a x i.val))
        (giantCandidatePrimeInterval (giantCandidateGroupHeight a x j.val))) := by
  intro i j hij
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with h | h
  · exact giantCandidatePrimeInterval_disjoint (giantCandidateGroupHeight_two_le_of_lt hx h)
  · exact (giantCandidatePrimeInterval_disjoint (giantCandidateGroupHeight_two_le_of_lt hx h)).symm

private theorem giantCandidate_small_big_disjoint {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    (i : GiantCandidateSmallGroupIndex x) (j : GiantCandidateBigGroupIndex x) :
    Disjoint (giantCandidateSmallGroup x i) (giantCandidateBigGroup x j) := by
  apply disjoint_left.mpr
  intro p hp hq
  have hlo := (giantCandidateBigGroup_range hx hlog hq).2.1
  have hhi := (giantCandidateSmallGroup_range hx hlog hp).2.2
  have hpow : (Real.log x)^(35/100:ℝ) ≤ (Real.log x)^(40/100:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
  exact (not_lt_of_ge ((Real.exp_le_exp.mpr hpow).trans hlo)) hhi

theorem giantCandidateGroup_pairwise_disjoint {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x) :
    Pairwise (fun i j => Disjoint (giantCandidateGroup x i) (giantCandidateGroup x j)) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · exact giantCandidate_same_family_disjoint (28/100) (35/100) x hx
      (fun h => hij (congrArg Sum.inl h))
  · exact giantCandidate_small_big_disjoint hx hlog i j
  · exact (giantCandidate_small_big_disjoint hx hlog j i).symm
  · exact giantCandidate_same_family_disjoint (40/100) (45/100) x hx
      (fun h => hij (congrArg Sum.inr h))

theorem giantCandidateFullPrimes_range {x : ℝ} (hx : 1 < x) (hlog : 1 ≤ Real.log x)
    {p : ℕ} (hp : p ∈ giantCandidateFullPrimes x) :
    p.Prime ∧ Real.exp ((Real.log x)^(28/100:ℝ)) ≤ (p:ℝ) ∧
      (p:ℝ) < Real.exp ((Real.log x)^(45/100:ℝ)) := by
  obtain ⟨i,hi⟩ := mem_giantCandidateFullPrimes.mp hp
  rcases i with i | i
  · obtain ⟨hP,hlo,hhi⟩ := giantCandidateSmallGroup_range hx hlog hi
    exact ⟨hP,hlo,hhi.trans_le (Real.exp_le_exp.mpr
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)))⟩
  · obtain ⟨hP,hlo,hhi⟩ := giantCandidateBigGroup_range hx hlog hi
    exact ⟨hP,(Real.exp_le_exp.mpr
      (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))).trans hlo,hhi⟩

theorem giantCandidateFullPrimes_prime_upper_eventually :
    ∀ᶠ x : ℝ in atTop,∀ p ∈ giantCandidateFullPrimes x,
      p.Prime ∧ (p:ℝ) ≤ Real.exp ((Real.log x)^(45/100:ℝ)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hx hlog
  exact fun p hp => ⟨(giantCandidateFullPrimes_range hx hlog hp).1,
    (giantCandidateFullPrimes_range hx hlog hp).2.2.le⟩

theorem giantCandidateFullPrimes_gt_W_eventually :
    ∀ᶠ x : ℝ in atTop,∀ p ∈ giantCandidateFullPrimes x,
      Real.exp ((Real.log x)^(6/25:ℝ)) < (p:ℝ) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1:ℝ))] with x hx hlog
  intro p hp
  exact (Real.exp_lt_exp.mpr
    (Real.rpow_lt_rpow_of_exponent_lt hlog (by norm_num))).trans_le
      (giantCandidateFullPrimes_range hx hlog.le hp).2.1

theorem giantCandidateFullPrimes_coprime_modulus_eventually (M : ℕ) (hM : 0 < M) :
    ∀ᶠ x : ℝ in atTop,∀ p ∈ giantCandidateFullPrimes x, p.Coprime M := by
  have hlarge := (Real.tendsto_exp_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<28/100)).comp Real.tendsto_log_atTop)).eventually
      (eventually_gt_atTop (M:ℝ))
  filter_upwards [hlarge,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with x hlarge hx hlog
  intro p hp
  obtain ⟨hP,hlo,_⟩ := giantCandidateFullPrimes_range hx hlog hp
  exact hP.coprime_iff_not_dvd.mpr (fun h => (not_lt_of_ge (Nat.cast_le.mpr (Nat.le_of_dvd hM h)))
    (hlarge.trans_le hlo))

theorem giantCandidateGroup_mass_eventually :
    ∀ᶠ x : ℝ in atTop,∀ i : GiantCandidateGroupIndex x,
      Real.log 2/2 < bandReciprocalMass (giantCandidateGroup x i) ∧
        bandReciprocalMass (giantCandidateGroup x i) < 1 := by
  obtain ⟨Y,hY⟩ := eventually_atTop.mp giantCandidatePrimeInterval_mass_eventually
  have hS := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<28/100)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop Y)
  have hB := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<40/100)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop Y)
  filter_upwards [hS,hB,eventually_gt_atTop (1:ℝ)] with x hs hb hx
  intro i
  rcases i with i | i
  · exact hY _ (hs.trans (giantCandidateGroupHeight_ge (28/100) x hx i.val))
  · exact hY _ (hb.trans (giantCandidateGroupHeight_ge (40/100) x hx i.val))

theorem giantCandidateGroup_counts_eventually :
    ∀ᶠ x : ℝ in atTop,
      ((35/100-28/100:ℝ)/(2*Real.log 2))*Real.log (Real.log x) ≤
        (Fintype.card (GiantCandidateSmallGroupIndex x):ℝ) ∧
      (Fintype.card (GiantCandidateSmallGroupIndex x):ℝ) ≤
        ((35/100-28/100:ℝ)/Real.log 2)*Real.log (Real.log x) ∧
      ((45/100-40/100:ℝ)/(2*Real.log 2))*Real.log (Real.log x) ≤
        (Fintype.card (GiantCandidateBigGroupIndex x):ℝ) ∧
      (Fintype.card (GiantCandidateBigGroupIndex x):ℝ) ≤
        ((45/100-40/100:ℝ)/Real.log 2)*Real.log (Real.log x) := by
  filter_upwards [giantCandidateGroupCount_bounds_eventually (28/100) (35/100) (by norm_num),
    giantCandidateGroupCount_bounds_eventually (40/100) (45/100) (by norm_num)] with x hs hb
  simpa only [Fintype.card_fin] using And.intro hs.1 (And.intro hs.2 hb)

end
end ArtinMatthews
