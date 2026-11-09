module

public import ArtinMatthews.MarkedRootUniformGrid


set_option backward.privateInPublic true
@[expose] public section

/-! A faithful left-closed grid: upper endpoints belong to the next
interval, except that the final interval includes the outer endpoint. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def markedRootPartitionInterval (N K : ℕ) (i : Fin K) (s : ℝ) : Set ℝ :=
  {x | s+(i:ℝ)/N ≤ x ∧
    if (i:ℕ)+1=K then x ≤ s+((i:ℝ)+1)/N else x < s+((i:ℝ)+1)/N}

theorem markedRootPartitionInterval_closed (N K : ℕ) (i : Fin K) (s : ℝ) :
    markedRootPartitionInterval N K i s ⊆ Set.Icc (s+(i:ℝ)/N) (s+((i:ℝ)+1)/N) := by
  intro x hx
  refine ⟨hx.1,?_⟩
  by_cases hi : (i:ℕ)+1=K
  · simpa only [ite_eq_left hi] using hx.2
  · have hh : x < s+((i:ℝ)+1)/N := by simpa only [ite_eq_right hi] using hx.2
    exact hh.le

theorem markedRootPartitionInterval_cover (N k : ℕ) (hN : 0 < N) (hk : 0 < k)
    (s x : ℝ) (hx : x ∈ Set.Icc s (s+k)) :
    ∃ i : Fin (k*N),x ∈ markedRootPartitionInterval N (k*N) i s := by
  have hNr : 0 < (N:ℝ) := by exact_mod_cast hN
  have hkn : 0 < k*N := Nat.mul_pos hk hN
  let t := (x-s)*(N:ℝ)
  have ht : 0 ≤ t := mul_nonneg (sub_nonneg.mpr hx.1) hNr.le
  let i := min ⌊t⌋₊ (k*N-1)
  have hi : i < k*N := (min_le_right _ _).trans_lt (by omega)
  refine ⟨⟨i,hi⟩,?_,?_⟩
  · have hie : (i:ℝ) ≤ t := (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le ht)
    have hh : (i:ℝ)/(N:ℝ) ≤ x-s := (div_le_iff₀ hNr).mpr hie
    linarith
  · by_cases hf : ⌊t⌋₊ ≤ k*N-1
    · have hie : i=⌊t⌋₊ := min_eq_left hf
      have hh : t < (i:ℝ)+1 := by rw [hie]; exact Nat.lt_floor_add_one t
      have hdiv : x-s < ((i:ℝ)+1)/(N:ℝ) := (lt_div_iff₀ hNr).mpr hh
      change if i+1=k*N then x ≤ s+((i:ℝ)+1)/N else x < s+((i:ℝ)+1)/N
      split_ifs <;> linarith
    · have hie : i=k*N-1 := min_eq_right (le_of_not_ge hf)
      have hip : i+1=k*N := by rw [hie]; omega
      change if i+1=k*N then x ≤ s+((i:ℝ)+1)/N else _
      rw [ite_eq_left hip]
      have hipr : (i:ℝ)+1=(k:ℝ)*N := by exact_mod_cast hip
      rw [hipr,mul_div_cancel_right₀ _ hNr.ne']
      exact hx.2

theorem markedRootPartitionInterval_unique (N K : ℕ) (hN : 0 < N) (s x : ℝ)
    (i j : Fin K) (hi : x ∈ markedRootPartitionInterval N K i s)
    (hj : x ∈ markedRootPartitionInterval N K j s) : i=j := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hnot (i j : Fin K) (hi : x ∈ markedRootPartitionInterval N K i s)
      (hj : x ∈ markedRootPartitionInterval N K j s) : ¬i.val<j.val := by
    intro hij
    have hlast : (i:ℕ)+1 ≠ K := by omega
    have hix : x < s+((i:ℝ)+1)/N := by simpa only [ite_eq_right hlast] using hi.2
    have hnum : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
    have hd := div_le_div_of_nonneg_right hnum hn.le
    linarith [hj.1]
  apply Fin.ext
  exact le_antisymm (le_of_not_gt (hnot j i hj hi)) (le_of_not_gt (hnot i j hi hj))

theorem markedRootPartitionInterval_measurable (N K : ℕ) (i : Fin K) (s : ℝ) :
    MeasurableSet (markedRootPartitionInterval N K i s) := by
  unfold markedRootPartitionInterval
  split_ifs <;> measurability

end ArtinMatthews
