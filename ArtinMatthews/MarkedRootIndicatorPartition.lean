module

public import ArtinMatthews.MarkedRootPartitionCount
public import ArtinMatthews.MarkedRootPartitionUnions


set_option backward.privateInPublic true
@[expose] public section

/-! Exact finite root and volume decompositions of an indicator. On bad
cells only positivity is used; elsewhere literal cell constancy suffices. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRootIndicatorCount {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V : ℝ) (T : Set (ℝ × (ℝ × ℝ))) : ℕ :=
  ((fixedURootMatrixBoxPoints g₀ U (16*U) 0 1 V (2*V) true true true true true true).filter
    (fun p => markedRootNormalizedPoint U V p ∈ T)).card

def markedRootCellIndicatorCount {S : ℕ} (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S))
    (U V : ℝ) (N : ℕ) (i : MarkedRootGridIndex N) (T : Set (ℝ × (ℝ × ℝ))) : ℕ :=
  ((markedRootPartitionRootSet g₀ U V N i).filter (fun p => markedRootNormalizedPoint U V p ∈ T)).card

theorem markedRootIndicatorCount_sum {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) {U V : ℝ}
    (hU : 1 < U) (hV : 1 < V) (N : ℕ) (hN : 0 < N) (T : Set (ℝ × (ℝ × ℝ))) :
    (markedRootIndicatorCount g₀ U V T:ℝ) =
      ∑ i : MarkedRootGridIndex N,(markedRootCellIndicatorCount g₀ U V N i T:ℝ) := by
  have hh := markedRootPartitionRootSet_sum g₀ hU hV N hN
    (fun p => if markedRootNormalizedPoint U V p ∈ T then (1:ℂ) else 0)
  have hc : (markedRootIndicatorCount g₀ U V T:ℂ) =
      ∑ i : MarkedRootGridIndex N,(markedRootCellIndicatorCount g₀ U V N i T:ℂ) := by
    simpa only [markedRootIndicatorCount,markedRootCellIndicatorCount,← Finset.sum_filter,
      Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  exact_mod_cast hc

theorem markedRootIndicatorVolume_sum (N : ℕ) (hN : 0 < N) (T : Set (ℝ × (ℝ × ℝ)))
    (hT : MeasurableSet T) (hsub : T ⊆ markedRootBoxDomain) :
    markedNormalizedRootMeasure.real T =
      ∑ i : MarkedRootGridIndex N,markedNormalizedRootMeasure.real (T ∩ markedRootPartitionCell N i) := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  have he : T = ⋃ i : MarkedRootGridIndex N,T ∩ markedRootPartitionCell N i := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,hi⟩ := markedRootPartitionCell_cover N hN (hsub hp)
      exact Set.mem_iUnion.mpr ⟨i,hp,hi⟩
    · intro hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      exact hi.1
  rw [he,measureReal_iUnion_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← he]
  · intro i j hij
    exact (markedRootPartitionCell_pairwise N hN hij).mono Set.inter_subset_right Set.inter_subset_right
  · intro i
    exact hT.inter (markedRootPartitionCell_measurable N i)

theorem markedRoot_indicator_cell_abs {a A b B d : ℝ}
    (ha : 0 ≤ a) (haA : a ≤ A) (hb : 0 ≤ b) (hbB : b ≤ B) (hd : 0 ≤ d) :
    |a-d*b| ≤ |A-d*B|+d*B := by
  have hdb := mul_le_mul_of_nonneg_left hbB hd
  have hdb0 := mul_nonneg hd hb
  have hu := le_abs_self (A-d*B)
  apply abs_le.mpr
  constructor <;> linarith [abs_nonneg (A-d*B)]

theorem markedRootIndicator_discrepancy {S : ℕ}
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) {U V : ℝ}
    (hU : 1 < U) (hV : 1 < V) (N : ℕ) (hN : 0 < N)
    (T : Set (ℝ × (ℝ × ℝ))) (hT : MeasurableSet T) (hsub : T ⊆ markedRootBoxDomain)
    (B : Finset (MarkedRootGridIndex N))
    (hc : ∀ i ∉ B,∀ p ∈ markedRootPartitionCell N i,∀ q ∈ markedRootPartitionCell N i,p ∈ T ↔ q ∈ T)
    (hd : 0 ≤ U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))) :
    |(markedRootIndicatorCount g₀ U V T:ℝ)-
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
        markedNormalizedRootMeasure.real T| ≤
      (∑ i : MarkedRootGridIndex N,markedRootPartitionCountError g₀ U V N i)+
      (U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ)))*
        markedNormalizedRootMeasure.real (markedRootPartitionUnion N B) := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  let d := U*V/((riemannZeta 2).re*(Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)):ℝ))
  have hroot (i : MarkedRootGridIndex N) (p : Σ _u : ℤ,ℤ × ℤ)
      (hp : p ∈ markedRootPartitionRootSet g₀ U V N i) :
      markedRootNormalizedPoint U V p ∈ markedRootPartitionCell N i := by
    rw [← markedRootPartitionRootSet_eq_filter g₀ hU hV N hN i] at hp
    exact (Finset.mem_filter.mp hp).2
  have herr (i : MarkedRootGridIndex N) : markedRootPartitionCountError g₀ U V N i =
      |((markedRootPartitionRootSet g₀ U V N i).card:ℝ)-d*(1/(N:ℝ)^3)| := by
    unfold markedRootPartitionCountError d
    congr 1
    ring
  have hcell (i : MarkedRootGridIndex N) :
      |(markedRootCellIndicatorCount g₀ U V N i T:ℝ)-d*markedNormalizedRootMeasure.real (T ∩ markedRootPartitionCell N i)| ≤
      markedRootPartitionCountError g₀ U V N i+(if i ∈ B then d*(1/(N:ℝ)^3) else 0) := by
    by_cases hi : i ∈ B
    · rw [ite_eq_left hi,herr]
      apply markedRoot_indicator_cell_abs (Nat.cast_nonneg _)
        (Nat.cast_le.mpr (Finset.card_filter_le _ _)) measureReal_nonneg
        ((measureReal_mono Set.inter_subset_right (measure_ne_top _ _)).trans_eq
          (markedRootPartitionCell_real_volume N hN i)) hd
    · rw [ite_eq_right hi,add_zero]
      by_cases hex : ∃ p ∈ markedRootPartitionCell N i,p ∈ T
      · obtain ⟨p,hp,hpT⟩ := hex
        have hall : ∀ q ∈ markedRootPartitionCell N i,q ∈ T := fun q hq => (hc i hi p hp q hq).mp hpT
        have he : T ∩ markedRootPartitionCell N i = markedRootPartitionCell N i := Set.inter_eq_right.mpr hall
        have hr : markedRootCellIndicatorCount g₀ U V N i T = (markedRootPartitionRootSet g₀ U V N i).card := by
          unfold markedRootCellIndicatorCount
          rw [Finset.filter_eq_self.mpr (fun q hq => hall _ (hroot i q hq))]
        rw [hr,he,markedRootPartitionCell_real_volume N hN i,herr]
      · have hno : ∀ p ∈ markedRootPartitionCell N i,p ∉ T := fun p hp ht => hex ⟨p,hp,ht⟩
        have he : T ∩ markedRootPartitionCell N i = ∅ := Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hno p hp.2 hp.1)
        have hr : markedRootCellIndicatorCount g₀ U V N i T = 0 := by
          unfold markedRootCellIndicatorCount
          rw [Finset.filter_false_of_mem (fun q hq => hno (markedRootNormalizedPoint U V q) (hroot i q hq)),Finset.card_empty]
        rw [hr,he,measureReal_empty,Nat.cast_zero,mul_zero,sub_zero,abs_zero]
        exact abs_nonneg _
  rw [markedRootIndicatorCount_sum g₀ hU hV N hN T,markedRootIndicatorVolume_sum N hN T hT hsub,
    Finset.mul_sum,← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => hcell i)).trans_eq
  rw [Finset.sum_add_distrib,markedRootPartitionUnion_real_volume N hN B]
  congr 1
  simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.filter_mem_eq_inter,Finset.univ_inter,
    Finset.sum_const,nsmul_eq_mul]
  ring

end ArtinMatthews
