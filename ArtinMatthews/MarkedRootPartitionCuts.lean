module

public import ArtinMatthews.MarkedRootPartitionVolume
public import ArtinMatthews.MarkedRawGoodArcFamily


set_option backward.privateInPublic true
@[expose] public section

/-! Faithful cells meeting an actual Möbius cut. Their union has the
derived one-dimensional tube bound, and every other cell preserves goodness. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
attribute [local instance] Classical.propDecidable

def markedRootPartitionCutIndices (N : ℕ) (cuts : Finset ℝ) : Finset (MarkedRootGridIndex N) :=
  Finset.univ.filter (fun i => ∃ c ∈ cuts,c ∈ Set.Icc ((i.1:ℝ)/N) (((i.1:ℝ)+1)/N))

def markedRootPartitionCutUnion (N : ℕ) (cuts : Finset ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  ⋃ i ∈ markedRootPartitionCutIndices N cuts,markedRootPartitionCell N i

theorem markedRootPartitionCutUnion_subset (N : ℕ) (cuts : Finset ℝ) :
    markedRootPartitionCutUnion N cuts ⊆ markedRootCutNeighborhood cuts (1/(N:ℝ)) ×ˢ Set.univ := by
  intro p hp
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
  obtain ⟨hi,hp⟩ := Set.mem_iUnion.mp hi
  obtain ⟨c,hc,hci⟩ := (Finset.mem_filter.mp hi).2
  have hpi := (markedRootPartitionCell_closed N i hp).1
  have hh := markedRootGrid_interval_close N i.1 0 p.1 c
    (by simpa only [zero_add] using hpi) (by simpa only [zero_add] using hci)
  refine ⟨Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩,Set.mem_univ _⟩
  exact ⟨by linarith [(abs_le.mp hh).1],by linarith [(abs_le.mp hh).2]⟩

theorem markedRootCutTube_measure_le (cuts : Finset ℝ) {h : ℝ} (hh : 0 ≤ h) :
    markedNormalizedRootMeasure (markedRootCutNeighborhood cuts h ×ˢ Set.univ) ≤
      ENNReal.ofReal (30*(cuts.card:ℝ)*h) := by
  unfold markedNormalizedRootMeasure
  rw [Measure.prod_prod]
  have hmass : ((volume.restrict (Set.Icc (1:ℝ) 16)).prod
      (volume.restrict (Set.Icc (1:ℝ) 2))) Set.univ = 15 := by
    rw [← Set.univ_prod_univ,Measure.prod_prod]
    simp only [Measure.restrict_apply_univ,Real.volume_Icc]
    norm_num
  rw [hmass]
  calc
    _ ≤ volume (markedRootCutNeighborhood cuts h)*15 := mul_le_mul' (Measure.restrict_apply_le _ _) le_rfl
    _ ≤ ENNReal.ofReal (2*(cuts.card:ℝ)*h)*15 :=
      mul_le_mul' (markedRootCutNeighborhood_volume_le cuts hh) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_ofNat,← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*(cuts.card:ℝ)*h)]
      congr 1
      ring

theorem markedRootPartitionCutUnion_measure_le (N : ℕ) (cuts : Finset ℝ) :
    markedNormalizedRootMeasure (markedRootPartitionCutUnion N cuts) ≤
      ENNReal.ofReal (30*(cuts.card:ℝ)/(N:ℝ)) := by
  apply (measure_mono (markedRootPartitionCutUnion_subset N cuts)).trans
  simpa only [div_eq_mul_inv,one_mul,mul_assoc] using
    markedRootCutTube_measure_le cuts (by positivity : 0 ≤ 1/(N:ℝ))

theorem markedRootPartitionCut_off_segment (N : ℕ) (cuts : Finset ℝ) (i : MarkedRootGridIndex N)
    (hi : i ∉ markedRootPartitionCutIndices N cuts) (p q : ℝ × (ℝ × ℝ))
    (hp : p ∈ markedRootPartitionCell N i) (hq : q ∈ markedRootPartitionCell N i) :
    ∀ t ∈ Set.uIcc p.1 q.1,t ∉ cuts := by
  intro t ht hc
  apply hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ i,t,hc,?_⟩
  have hpi := (markedRootPartitionCell_closed N i hp).1
  have hqi := (markedRootPartitionCell_closed N i hq).1
  rcases Set.mem_uIcc.mp ht with ht | ht
  · exact ⟨hpi.1.trans ht.1,ht.2.trans hqi.2⟩
  · exact ⟨hqi.1.trans ht.1,ht.2.trans hpi.2⟩

theorem markedRawCircleGood_partition_constancy {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y R : ℝ)
    (z w : Fin 2 → ℝ) (hdet : markedVectorDet z w=1) (N : ℕ) (i : MarkedRootGridIndex N)
    (hi : i ∉ markedRootPartitionCutIndices N
      (markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x a d₀ Y R)))
    (p q : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootPartitionCell N i) (hq : q ∈ markedRootPartitionCell N i)
    (hR : 0 ≤ R) (hfirst : Y^(-7/10:ℝ) ≤ 1)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) ≤ 1)
    (hr : |markedTransportedRatio p.1 z w| ≤ R) (hs : |markedTransportedRatio q.1 z w| ≤ R) :
    MarkedRawCircleGood e x a d₀ Y (markedTransportedRatio p.1 z w:AddCircle (1:ℝ)) ↔
      MarkedRawCircleGood e x a d₀ Y (markedTransportedRatio q.1 z w:AddCircle (1:ℝ)) := by
  exact markedRawCircleGood_transport_constancy e x a d₀ Y R z w hdet hR hfirst hbeta hr hs
    (markedRootPartitionCut_off_segment N _ i hi p q hp hq)

end ArtinMatthews
