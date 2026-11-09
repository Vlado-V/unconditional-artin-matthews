module

public import ArtinMatthews.MarkedRootArcIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! Exact closed-interval decomposition of a short signed root arc on
[0,1].  The two end intervals are clipped, so wrapping through zero is
represented without changing endpoint conventions or multiplicities. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootArcCenters (n : ℕ) : Finset ℤ := Finset.Icc 0 (n:ℤ)

def markedRootArcLower (n : ℕ) (ε : ℝ) (k : ℤ) : ℝ := max 0 (((k:ℝ)-ε)/n)

def markedRootArcUpper (n : ℕ) (ε : ℝ) (k : ℤ) : ℝ := min 1 (((k:ℝ)+ε)/n)

def markedRootArcClippedInterval (n : ℕ) (ε : ℝ) (k : ℤ) : Set ℝ :=
  Set.Icc (markedRootArcLower n ε k) (markedRootArcUpper n ε k)

theorem markedRootArcClippedInterval_iff {n : ℕ} {ε r : ℝ} {k : ℤ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    r ∈ markedRootArcClippedInterval n ε k ↔ r ∈ markedRootArcInterval n ε k := by
  simp only [markedRootArcClippedInterval,markedRootArcLower,markedRootArcUpper,
    markedRootArcInterval,Set.mem_Icc,max_le_iff,le_min_iff]
  tauto

theorem markedRootArcClippedInterval_bounds {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 ≤ ε)
    {k : ℤ} (hk : k ∈ markedRootArcCenters n) :
    0 ≤ markedRootArcLower n ε k ∧ markedRootArcLower n ε k ≤ markedRootArcUpper n ε k ∧
      markedRootArcUpper n ε k ≤ 1 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨hk₀,hk₁⟩ := Finset.mem_Icc.mp hk
  have hkR₀ : (0:ℝ)≤k := by exact_mod_cast hk₀
  have hkR₁ : (k:ℝ)≤n := by exact_mod_cast hk₁
  have hc₀ : (0:ℝ)≤(k:ℝ)/n := div_nonneg hkR₀ hnR.le
  have hc₁ : (k:ℝ)/n≤1 := (div_le_one hnR).mpr hkR₁
  have hl : ((k:ℝ)-ε)/n≤(k:ℝ)/n := div_le_div_of_nonneg_right (by linarith) hnR.le
  have hu : (k:ℝ)/n≤((k:ℝ)+ε)/n := div_le_div_of_nonneg_right (by linarith) hnR.le
  exact ⟨le_max_left _ _,(max_le hc₀ hl).trans (le_min hc₁ hu),min_le_left _ _⟩

theorem markedRootArcCenters_card (n : ℕ) : (markedRootArcCenters n).card = n+1 := by
  simp [markedRootArcCenters,Int.card_Icc]

theorem markedBadRootMultiple_clipped_cover (q : ℤ) (hq : q ≠ 0)
    {ε r : ℝ} (hε : ε < 1) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) :
    (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε ↔
      ∃ k ∈ markedRootArcCenters q.natAbs,r ∈ markedRootArcClippedInterval q.natAbs ε k := by
  rw [markedBadRootMultiple_natAbs]
  have hn := Int.natAbs_pos.mpr hq
  have hnR : (0:ℝ)<q.natAbs := by exact_mod_cast hn
  constructor
  · intro h
    obtain ⟨k,_,hk⟩ := (markedBadRootMultiple_nat_interval_cover hn hε.le hr₀ hr₁).mp h
    have hd := abs_le.mp ((markedRootArcInterval_iff hn ε r k).mp hk)
    have hp₀ : 0 ≤ (q.natAbs:ℝ)*r := mul_nonneg hnR.le hr₀
    have hp₁ : (q.natAbs:ℝ)*r ≤ q.natAbs := by nlinarith
    have hklo : (-1:ℝ)<k := by linarith
    have hkhi : (k:ℝ)<(q.natAbs:ℝ)+1 := by linarith
    have hkloZ : (-1:ℤ)<k := by exact_mod_cast hklo
    have hkhiZ : k<(q.natAbs:ℤ)+1 := by
      apply (Int.cast_lt (R := ℝ)).mp
      simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hkhi
    refine ⟨k,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    exact (markedRootArcClippedInterval_iff hr₀ hr₁).mpr hk
  · rintro ⟨k,hk,hr⟩
    apply (markedBadRootMultiple_nat_interval_cover hn hε.le hr₀ hr₁).mpr
    refine ⟨k,?_,(markedRootArcClippedInterval_iff hr₀ hr₁).mp hr⟩
    obtain ⟨hk₀,hk₁⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

theorem markedRootArcClippedInterval_unique {n : ℕ} (hn : 0 < n) {ε r : ℝ}
    (hε : ε < (1/2:ℝ)) {k l : ℤ}
    (hk : r ∈ markedRootArcClippedInterval n ε k)
    (hl : r ∈ markedRootArcClippedInterval n ε l) : k=l := by
  have hr₀ : 0 ≤ r := (le_max_left _ _).trans hk.1
  have hr₁ : r ≤ 1 := hl.2.trans (min_le_left _ _)
  have hkd := abs_le.mp ((markedRootArcInterval_iff hn ε r k).mp
    ((markedRootArcClippedInterval_iff hr₀ hr₁).mp hk))
  have hld := abs_le.mp ((markedRootArcInterval_iff hn ε r l).mp
    ((markedRootArcClippedInterval_iff hr₀ hr₁).mp hl))
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hz : (k:ℝ)+1≤l := by exact_mod_cast (Int.add_one_le_iff.mpr hkl)
    linarith
  · exact hkl
  · have hz : (l:ℝ)+1≤k := by exact_mod_cast (Int.add_one_le_iff.mpr hkl)
    linarith

theorem markedRootArcClippedInterval_pairwise {n : ℕ} (hn : 0 < n) {ε : ℝ}
    (hε : ε < (1/2:ℝ)) :
    Pairwise (fun k l : ℤ => Disjoint (markedRootArcClippedInterval n ε k)
      (markedRootArcClippedInterval n ε l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro r hrk hrl
  exact hkl (markedRootArcClippedInterval_unique hn hε hrk hrl)

theorem markedBadRootMultiple_clipped_indicator {E : Type*} [AddCommMonoid E]
    (q : ℤ) (hq : q ≠ 0) {ε r : ℝ} (hε : ε < (1/2:ℝ))
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) (c : E) :
    (if (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε then c else 0) =
      ∑ k ∈ markedRootArcCenters q.natAbs,
        if r ∈ markedRootArcClippedInterval q.natAbs ε k then c else 0 := by
  have hc := markedBadRootMultiple_clipped_cover q hq (hε.trans (by norm_num)) hr₀ hr₁
  by_cases h : (r:AddCircle (1:ℝ)) ∈ markedBadRootMultiple q ε
  · obtain ⟨k,hk,hrk⟩ := hc.mp h
    rw [ite_eq_left h,Finset.sum_eq_single k]
    · rw [ite_eq_left hrk]
    · intro l _ hl
      have hrl : r ∉ markedRootArcClippedInterval q.natAbs ε l := by
        intro hrl
        exact hl (markedRootArcClippedInterval_unique (Int.natAbs_pos.mpr hq) hε hrl hrk)
      rw [ite_eq_right hrl]
    · exact fun hk' => (hk' hk).elim
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hrk : r ∉ markedRootArcClippedInterval q.natAbs ε k := fun hr => h (hc.mpr ⟨k,hk,hr⟩)
    rw [ite_eq_right hrk]

theorem markedRootArcClipped_coefficient_mass (q : ℤ) (c : ℂ) :
    (∑ _k ∈ markedRootArcCenters q.natAbs,‖c‖) = (q.natAbs+1:ℕ)*‖c‖ := by
  simp [markedRootArcCenters_card]

theorem markedBadRootMultiple_zero (ε : ℝ) :
    markedBadRootMultiple 0 ε = if 0 ≤ ε then Set.univ else ∅ := by
  ext θ
  simp [markedBadRootMultiple]

end
end ArtinMatthews
