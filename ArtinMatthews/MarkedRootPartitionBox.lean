module

public import ArtinMatthews.MarkedRootPartitionCells
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt


set_option backward.privateInPublic true
@[expose] public section

/-! The literal transported physical box is constant on every grid cell
that misses its actual moving faces. No boundary regularity is assumed. -/

noncomputable section
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

def MarkedRootPhysicalBox (U V : ℝ) (z : Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : Prop :=
  markedRootBoxFirst z p ∈ Set.Icc (1:ℝ) 16 ∧ markedRootBoxSecond U V z p ∈ Set.Icc (1:ℝ) 2

theorem markedRootPhysicalBox_boundary (U V : ℝ) (z : Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) :
    (markedRootBoxFirst z p,markedRootBoxSecond U V z p) ∈
      frontier (Set.Icc (1:ℝ) 16 ×ˢ Set.Icc (1:ℝ) 2) ↔
      p ∈ markedRootPhysicalBoxBoundary U V z := by
  rw [frontier_prod_eq,frontier_Icc (by norm_num : (1:ℝ) ≤ 16),
    frontier_Icc (by norm_num : (1:ℝ) ≤ 2),closure_Icc,closure_Icc]
  simp only [Set.mem_union,Set.mem_prod,Set.mem_insert_iff,Set.mem_singleton_iff,
    markedRootPhysicalBoxBoundary,Set.mem_ofPred_eq]
  exact or_comm

theorem markedRootGridCell_preconnected (N : ℕ) (i : MarkedRootGridIndex N) :
    IsPreconnected (markedRootGridCell N i) := by
  have hc : Convex ℝ (markedRootGridCell N i) := by
    change Convex ℝ ((Set.Icc ((i.1:ℝ)/N) (((i.1:ℝ)+1)/N)) ×ˢ
      ((Set.Icc (1+(i.2.1:ℝ)/N) (1+((i.2.1:ℝ)+1)/N)) ×ˢ
        (Set.Icc (1+(i.2.2:ℝ)/N) (1+((i.2.2:ℝ)+1)/N))))
    exact (convex_Icc _ _).prod ((convex_Icc _ _).prod (convex_Icc _ _))
  exact hc.isPreconnected

theorem markedRootPhysicalBox_grid_constancy (N : ℕ) (hN : 0 < N)
    {U V : ℝ} (hU : U ≠ 0) (hV : V ≠ 0) (z : Fin 2 → ℝ) (i : MarkedRootGridIndex N)
    (hi : i ∉ markedRootBadGridIndices N U V z) (p q : ℝ × (ℝ × ℝ))
    (hp : p ∈ markedRootGridCell N i) (hq : q ∈ markedRootGridCell N i) :
    MarkedRootPhysicalBox U V z p ↔ MarkedRootPhysicalBox U V z q := by
  let f : (ℝ × (ℝ × ℝ)) → ℝ × ℝ := fun t =>
    (markedRootBoxFirst z t,markedRootBoxSecond U V z t)
  let B : Set (ℝ × ℝ) := Set.Icc (1:ℝ) 16 ×ˢ Set.Icc (1:ℝ) 2
  have hB : IsClosed B := isClosed_Icc.prod isClosed_Icc
  have hf : ContinuousOn f (markedRootGridCell N i) := by
    apply ContinuousOn.prodMk
    · unfold markedRootBoxFirst markedTau
      fun_prop
    · unfold markedRootBoxSecond
      apply ContinuousOn.add
      · unfold markedTau
        fun_prop
      · apply continuousOn_const.div (by fun_prop)
        intro t ht
        have ha := (markedRootGridCell_subset N hN i ht).2.1.1
        exact mul_ne_zero (mul_ne_zero hU hV) (by linarith)
  have hnot (t : ℝ × (ℝ × ℝ)) (ht : t ∈ markedRootGridCell N i) : f t ∉ frontier B := by
    intro hb
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,t,ht,(markedRootPhysicalBox_boundary U V z t).mp hb⟩
  have hcover : f '' markedRootGridCell N i ⊆ interior B ∪ Bᶜ := by
    rintro _ ⟨t,ht,rfl⟩
    by_cases hb : f t ∈ B
    · left
      by_contra hn
      exact hnot t ht ⟨subset_closure hb,hn⟩
    · exact Or.inr hb
  have hdis : Disjoint (interior B) Bᶜ := Set.disjoint_left.mpr (fun _ hb hc => hc (interior_subset hb))
  obtain hin | hout := (markedRootGridCell_preconnected N i).image f hf |>.subset_or_subset
    isOpen_interior hB.isOpen_compl hdis hcover
  · have hpin : f p ∈ B := interior_subset (hin (Set.mem_image_of_mem f hp))
    have hqin : f q ∈ B := interior_subset (hin (Set.mem_image_of_mem f hq))
    exact iff_of_true hpin hqin
  · exact iff_of_false (hout (Set.mem_image_of_mem f hp)) (hout (Set.mem_image_of_mem f hq))

theorem markedRootPhysicalBox_partition_constancy (N : ℕ) (hN : 0 < N)
    {U V : ℝ} (hU : U ≠ 0) (hV : V ≠ 0) (z : Fin 2 → ℝ) (i : MarkedRootGridIndex N)
    (hi : i ∉ markedRootBadGridIndices N U V z) (p q : ℝ × (ℝ × ℝ))
    (hp : p ∈ markedRootPartitionCell N i) (hq : q ∈ markedRootPartitionCell N i) :
    MarkedRootPhysicalBox U V z p ↔ MarkedRootPhysicalBox U V z q := by
  exact markedRootPhysicalBox_grid_constancy N hN hU hV z i hi p q
    (markedRootPartitionCell_closed N i hp) (markedRootPartitionCell_closed N i hq)

end ArtinMatthews
