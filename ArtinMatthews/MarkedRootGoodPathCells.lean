module

public import ArtinMatthews.MarkedRootPartitionUnions
public import ArtinMatthews.MarkedRootGoodBoxCells
public import ArtinMatthews.MarkedRootGoodBoxMeasure
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual finite path box/good indicators and their derived bad-cell
volume. Every first/beta test and every possible Möbius pole is retained. -/

noncomputable section
namespace ArtinMatthews
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J ι : Type*} [Fintype J] [DecidableEq J]
variable (e : J → ℝ) (x : ℝ) {M : ℕ}
variable (I : Finset ι) (a : ι → MarkedRawActive (markedRawActualPrimeBand e x) M)
variable (d₀ Y U V H : ℝ) (z w : ι → Fin 2 → ℝ)

def MarkedRootPhysicalGoodPath (p : ℝ × (ℝ × ℝ)) : Prop :=
  ∀ k ∈ I,MarkedRootPhysicalGoodBox e x (a k) d₀ Y U V (z k) (w k) p

def markedRootGoodPathBadIndices (N : ℕ) : Finset (MarkedRootGridIndex N) :=
  I.biUnion (fun k => markedRootBadGridIndices N U V (z k) ∪
    markedRootPartitionCutIndices N (markedTransportedRatioAllCuts (z k) (w k)
      (markedRawGoodArcLevels e x (a k) d₀ Y (64*H))))

def markedRootGoodPathBoundaryCost : ℝ :=
  40960*(I.card:ℝ)*H+30*∑ k ∈ I,
    ((markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (a k) d₀ Y (64*H))).card:ℝ)

theorem markedRootPhysicalGoodPath_measurable :
    MeasurableSet {p | MarkedRootPhysicalGoodPath e x I a d₀ Y U V z w p} := by
  simpa only [MarkedRootPhysicalGoodPath,Set.ofPred_forall] using
    Finset.measurableSet_biInter I (fun k _ => markedRootPhysicalGoodBox_measurable e x (a k) d₀ Y U V (z k) (w k))

theorem markedRootPhysicalGoodPath_cell_constancy
    (hU : U ≠ 0) (hV : V ≠ 0) (hH : 0 ≤ H)
    (hdet : ∀ k ∈ I,markedVectorDet (z k) (w k)=1)
    (hw : ∀ k ∈ I,∀ j,|w k j| ≤ H)
    (hfirst : Y^(-7/10:ℝ) ≤ 1)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) ≤ 1)
    (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N)
    (hi : i ∉ markedRootGoodPathBadIndices e x I a d₀ Y U V H z w N)
    (p q : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootPartitionCell N i) (hq : q ∈ markedRootPartitionCell N i) :
    MarkedRootPhysicalGoodPath e x I a d₀ Y U V z w p ↔
      MarkedRootPhysicalGoodPath e x I a d₀ Y U V z w q := by
  have hk (k : ι) (hki : k ∈ I) := markedRootPhysicalGoodBox_cell_constancy e x (a k) d₀ Y U V H
    hU hV hH (z k) (w k) (hdet k hki) (hw k hki) N hN i
    (fun hm => hi (Finset.mem_biUnion.mpr ⟨k,hki,Finset.mem_union_left _ hm⟩))
    (fun hm => hi (Finset.mem_biUnion.mpr ⟨k,hki,Finset.mem_union_right _ hm⟩))
    hfirst hbeta p q hp hq
  constructor
  · intro h k hki
    exact (hk k hki).mp (h k hki)
  · intro h k hki
    exact (hk k hki).mpr (h k hki)

theorem markedRootGoodPathBadUnion_real_volume_le (N : ℕ) (hN : 0 < N)
    (hUV : 1 ≤ U*V) (hH : 0 ≤ H) (hsmall : 20*H/(N:ℝ) ≤ 1/2)
    (hz : ∀ k ∈ I,∀ j,|z k j| ≤ H) :
    markedNormalizedRootMeasure.real
      (markedRootPartitionUnion N (markedRootGoodPathBadIndices e x I a d₀ Y U V H z w N)) ≤
      markedRootGoodPathBoundaryCost e x I a d₀ Y H z w/(N:ℝ) := by
  let : IsFiniteMeasure markedNormalizedRootMeasure := by
    unfold markedNormalizedRootMeasure
    infer_instance
  let B (k : ι) := markedRootBadGridUnion N U V (z k) ∪ markedRootPartitionCutUnion N
    (markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (a k) d₀ Y (64*H)))
  have hsub : markedRootPartitionUnion N (markedRootGoodPathBadIndices e x I a d₀ Y U V H z w N) ⊆
      ⋃ k ∈ I,B k := by
    intro p hp
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hi,hp⟩ := Set.mem_iUnion.mp hi
    obtain ⟨k,hki,hi⟩ := Finset.mem_biUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hki,?_⟩⟩
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,markedRootPartitionCell_closed N i hp⟩⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hp⟩⟩)
  have hf (k : ι) (hki : k ∈ I) :
      markedNormalizedRootMeasure.real (markedRootBadGridUnion N U V (z k)) ≤ 40960*H/(N:ℝ) := by
    have hh := markedRootBadGridUnion_measure_le N hN hUV hH hsmall (z k) (hz k hki)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hc (k : ι) : markedNormalizedRootMeasure.real (markedRootPartitionCutUnion N
      (markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (a k) d₀ Y (64*H)))) ≤
      30*((markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (a k) d₀ Y (64*H))).card:ℝ)/(N:ℝ) := by
    have hh := markedRootPartitionCutUnion_measure_le N
      (markedTransportedRatioAllCuts (z k) (w k) (markedRawGoodArcLevels e x (a k) d₀ Y (64*H)))
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (by positivity))
  calc
    _ ≤ markedNormalizedRootMeasure.real (⋃ k ∈ I,B k) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ k ∈ I,markedNormalizedRootMeasure.real (B k) := measureReal_biUnion_finset_le I B
    _ ≤ ∑ k ∈ I,(40960*H/(N:ℝ)+30*((markedTransportedRatioAllCuts (z k) (w k)
        (markedRawGoodArcLevels e x (a k) d₀ Y (64*H))).card:ℝ)/(N:ℝ)) := by
      apply Finset.sum_le_sum
      intro k hki
      exact (measureReal_union_le _ _).trans (add_le_add (hf k hki) (hc k))
    _ = _ := by
      unfold markedRootGoodPathBoundaryCost
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.sum_div,← Finset.mul_sum]
      ring

end ArtinMatthews
