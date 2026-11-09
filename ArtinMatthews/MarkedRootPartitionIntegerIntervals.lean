module

public import ArtinMatthews.MarkedRootPartitionIntervals
public import ArtinMatthews.FixedURootWeightedGeometry


set_option backward.privateInPublic true
@[expose] public section

/-! The half-open cell conventions match the actual arithmetic rectangle
flags exactly, including all integer endpoints. -/

noncomputable section
namespace ArtinMatthews
open OAI.Erdos970.ErdosHyperbolaError
attribute [local instance] Classical.propDecidable

theorem markedRoot_mem_integer_interval (A B : ℝ) (n : ℤ) (rc : Bool) :
    n ∈ realIntervalIntegers A B true rc ↔ A ≤ (n:ℝ) ∧
      if rc then (n:ℝ) ≤ B else (n:ℝ) < B := by
  cases rc
  · simp only [realIntervalIntegers,Finset.mem_filter,Finset.mem_Icc,Int.ceil_le,Int.le_floor,
      Bool.false_eq_true,ite_false,ite_true]
    constructor
    · rintro ⟨⟨hA,_⟩,_,hB⟩
      exact ⟨hA,hB⟩
    · rintro ⟨hA,hB⟩
      exact ⟨⟨hA,hB.le⟩,hA,hB⟩
  · simpa only [ite_true] using fixedURoot_mem_closed_interval A B n

theorem markedRootPartitionInterval_integer_iff (N K : ℕ) (i : Fin K)
    (s T : ℝ) (hT : 0 < T) (n : ℤ) :
    n ∈ realIntervalIntegers (T*(s+(i:ℝ)/N)) (T*(s+((i:ℝ)+1)/N)) true (decide ((i:ℕ)+1=K)) ↔
      (n:ℝ)/T ∈ markedRootPartitionInterval N K i s := by
  rw [markedRoot_mem_integer_interval]
  unfold markedRootPartitionInterval
  simp only [Set.mem_ofPred_eq]
  by_cases hi : (i:ℕ)+1=K
  · simp only [hi,decide_true,ite_true,le_div_iff₀ hT,div_le_iff₀ hT]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith
  · simp only [hi,decide_false,Bool.false_eq_true,ite_false,le_div_iff₀ hT,div_lt_iff₀ hT]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> nlinarith

end ArtinMatthews
