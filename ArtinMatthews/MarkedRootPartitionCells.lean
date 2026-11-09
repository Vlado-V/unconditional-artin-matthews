module

public import ArtinMatthews.MarkedRootPartitionIntervals


set_option backward.privateInPublic true
@[expose] public section

/-! A faithful finite partition of the normalized root box. Every point,
including an interior grid boundary, is assigned to exactly one cell. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootPartitionCell (N : ℕ) (i : MarkedRootGridIndex N) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.1 ∈ markedRootPartitionInterval N N i.1 0 ∧
    p.2.1 ∈ markedRootPartitionInterval N (15*N) i.2.1 1 ∧
    p.2.2 ∈ markedRootPartitionInterval N N i.2.2 1}

theorem markedRootPartitionInterval_cast (N K L : ℕ) (h : K=L) (i : Fin K) (s : ℝ) :
    markedRootPartitionInterval N L (Fin.cast h i) s = markedRootPartitionInterval N K i s := by
  cases h
  rfl

theorem markedRootPartitionCell_closed (N : ℕ) (i : MarkedRootGridIndex N) :
    markedRootPartitionCell N i ⊆ markedRootGridCell N i := by
  intro p hp
  exact ⟨by simpa only [zero_add] using markedRootPartitionInterval_closed N N i.1 0 hp.1,
    markedRootPartitionInterval_closed N (15*N) i.2.1 1 hp.2.1,
    markedRootPartitionInterval_closed N N i.2.2 1 hp.2.2⟩

theorem markedRootPartitionCell_cover (N : ℕ) (hN : 0 < N) {p : ℝ × (ℝ × ℝ)}
    (hp : p ∈ markedRootBoxDomain) : ∃ i : MarkedRootGridIndex N,p ∈ markedRootPartitionCell N i := by
  have hr : ∃ i : Fin N,p.1 ∈ markedRootPartitionInterval N N i 0 := by
    obtain ⟨i,hi⟩ := markedRootPartitionInterval_cover N 1 hN (by decide) 0 p.1 (by simpa using hp.1)
    refine ⟨Fin.cast (Nat.one_mul N) i,?_⟩
    rw [markedRootPartitionInterval_cast]
    exact hi
  have hb : ∃ i : Fin N,p.2.2 ∈ markedRootPartitionInterval N N i 1 := by
    obtain ⟨i,hi⟩ := markedRootPartitionInterval_cover N 1 hN (by decide) 1 p.2.2
      (by convert hp.2.2 using 1; norm_num)
    refine ⟨Fin.cast (Nat.one_mul N) i,?_⟩
    rw [markedRootPartitionInterval_cast]
    exact hi
  obtain ⟨r,hr⟩ := hr
  obtain ⟨a,ha⟩ := markedRootPartitionInterval_cover N 15 hN (by decide) 1 p.2.1
    (by convert hp.2.1 using 1; norm_num)
  obtain ⟨b,hb⟩ := hb
  exact ⟨(r,a,b),hr,ha,hb⟩

theorem markedRootPartitionCell_unique (N : ℕ) (hN : 0 < N) (i j : MarkedRootGridIndex N)
    (p : ℝ × (ℝ × ℝ)) (hi : p ∈ markedRootPartitionCell N i) (hj : p ∈ markedRootPartitionCell N j) : i=j := by
  apply Prod.ext
  · exact markedRootPartitionInterval_unique N N hN 0 p.1 i.1 j.1 hi.1 hj.1
  · apply Prod.ext
    · exact markedRootPartitionInterval_unique N (15*N) hN 1 p.2.1 i.2.1 j.2.1 hi.2.1 hj.2.1
    · exact markedRootPartitionInterval_unique N N hN 1 p.2.2 i.2.2 j.2.2 hi.2.2 hj.2.2

theorem markedRootPartitionCell_pairwise (N : ℕ) (hN : 0 < N) :
    Pairwise (fun i j : MarkedRootGridIndex N => Disjoint (markedRootPartitionCell N i) (markedRootPartitionCell N j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hi hj
  exact hij (markedRootPartitionCell_unique N hN i j p hi hj)

theorem markedRootPartitionCell_measurable (N : ℕ) (i : MarkedRootGridIndex N) :
    MeasurableSet (markedRootPartitionCell N i) := by
  exact (markedRootPartitionInterval_measurable N N i.1 0).preimage measurable_fst |>.inter
    (((markedRootPartitionInterval_measurable N (15*N) i.2.1 1).preimage measurable_snd.fst).inter
      ((markedRootPartitionInterval_measurable N N i.2.2 1).preimage measurable_snd.snd))

theorem markedRootPartitionCell_indicator_sum {E : Type*} [AddCommMonoid E]
    (N : ℕ) (hN : 0 < N) (p : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootBoxDomain) (c : E) :
    (∑ i : MarkedRootGridIndex N,if p ∈ markedRootPartitionCell N i then c else 0) = c := by
  obtain ⟨i,hi⟩ := markedRootPartitionCell_cover N hN hp
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    apply ite_eq_right
    intro hj
    exact hji (markedRootPartitionCell_unique N hN j i p hj hi)
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem markedRootPartitionCell_finite_sum {α E : Type*} [AddCommMonoid E]
    (N : ℕ) (hN : 0 < N) (P : Finset α) (v : α → ℝ × (ℝ × ℝ)) (f : α → E)
    (hP : ∀ p ∈ P,v p ∈ markedRootBoxDomain) :
    (∑ p ∈ P,f p) = ∑ i : MarkedRootGridIndex N,∑ p ∈ P.filter (fun p => v p ∈ markedRootPartitionCell N i),f p := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact (markedRootPartitionCell_indicator_sum N hN (v p) (hP p hp) (f p)).symm

end ArtinMatthews
