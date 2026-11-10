module

public import ArtinMatthews.MarkedRootPartitionBox
public import ArtinMatthews.MarkedRootPartitionCuts
public import ArtinMatthews.MarkedRootAffineStrip
public import ArtinMatthews.MarkedRootArcFamilies
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! Full actual first/beta goodness together with the moving physical
box is constant on a good cell. Its ratio range follows from the true box. -/

noncomputable section
namespace ArtinMatthews
open Filter
attribute [local instance] Classical.propDecidable

theorem markedTransportedRatio_box_bound {H : ℝ} (hH : 0 ≤ H)
    (z w : Fin 2 → ℝ) (hw : ∀ k,|w k| ≤ H) (p : ℝ × (ℝ × ℝ))
    (hp : p ∈ markedRootBoxDomain) (hx : (1/2:ℝ) ≤ markedRootBoxFirst z p) :
    |markedTransportedRatio p.1 z w| ≤ 64*H := by
  have hz : (1/32:ℝ) ≤ markedTau p.1 z := markedRoot_first_box_slope hp.2.1 hx
  have hzp : 0 < markedTau p.1 z := lt_of_lt_of_le (by norm_num) hz
  have hr : |p.1| ≤ 1 := by rw [abs_of_nonneg hp.1.1]; exact hp.1.2
  have ht : |markedTau p.1 w| ≤ 2*H := by
    calc
      _ ≤ |w 0|+|p.1*w 1| := abs_add_le _ _
      _ = |w 0|+|p.1| * |w 1| := by rw [abs_mul]
      _ ≤ H+1*H := add_le_add (hw 0) (mul_le_mul hr (hw 1) (abs_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [markedTransportedRatio,abs_div,abs_of_pos hzp]
  apply (div_le_iff₀ hzp).mpr
  nlinarith [mul_le_mul_of_nonneg_left hz (show 0 ≤ 64*H by positivity)]

def MarkedRootPhysicalGoodBox {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V : ℝ)
    (z w : Fin 2 → ℝ) (p : ℝ × (ℝ × ℝ)) : Prop :=
  MarkedRootPhysicalBox U V z p ∧
    MarkedRawCircleGood e x a d₀ Y (markedTransportedRatio p.1 z w:AddCircle (1:ℝ))

theorem markedRootPhysicalGoodBox_cell_constancy {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x : ℝ) {M : ℕ}
    (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V H : ℝ)
    (hU : U ≠ 0) (hV : V ≠ 0) (hH : 0 ≤ H) (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w=1) (hw : ∀ k,|w k| ≤ H)
    (N : ℕ) (hN : 0 < N) (i : MarkedRootGridIndex N)
    (hface : i ∉ markedRootBadGridIndices N U V z)
    (hcut : i ∉ markedRootPartitionCutIndices N
      (markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x a d₀ Y (64*H))))
    (hfirst : Y^(-7/10:ℝ) ≤ 1)
    (hbeta : ∀ j,100*Real.exp (-((Real.log x)^(e j))) ≤ 1)
    (p q : ℝ × (ℝ × ℝ)) (hp : p ∈ markedRootPartitionCell N i) (hq : q ∈ markedRootPartitionCell N i) :
    MarkedRootPhysicalGoodBox e x a d₀ Y U V z w p ↔
      MarkedRootPhysicalGoodBox e x a d₀ Y U V z w q := by
  have hb := markedRootPhysicalBox_partition_constancy N hN hU hV z i hface p q hp hq
  by_cases hbp : MarkedRootPhysicalBox U V z p
  · have hbq := hb.mp hbp
    have hpd := markedRootGridCell_subset N hN i (markedRootPartitionCell_closed N i hp)
    have hqd := markedRootGridCell_subset N hN i (markedRootPartitionCell_closed N i hq)
    have hpr := markedTransportedRatio_box_bound hH z w hw p hpd (by linarith [hbp.1.1])
    have hqr := markedTransportedRatio_box_bound hH z w hw q hqd (by linarith [hbq.1.1])
    have hg := markedRawCircleGood_partition_constancy e x a d₀ Y (64*H) z w hdet N i hcut
      p q hp hq (by positivity) hfirst hbeta hpr hqr
    exact and_congr hb hg
  · have hbq : ¬MarkedRootPhysicalBox U V z q := fun h => hbp (hb.mpr h)
    simp only [MarkedRootPhysicalGoodBox,hbp,hbq,false_and]

theorem markedRootPhysicalGoodBox_actual_constancy {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) :
    ∀ᶠ x : ℝ in atTop,∀ {M : ℕ}
      (a : MarkedRawActive (markedRawActualPrimeBand e x) M) (d₀ Y U V H : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → U ≠ 0 → V ≠ 0 → 0 ≤ H →
      ∀ (z w : Fin 2 → ℝ),markedVectorDet z w=1 → (∀ k,|w k| ≤ H) →
      ∀ (N : ℕ),0 < N → ∀ (i : MarkedRootGridIndex N),
      i ∉ markedRootBadGridIndices N U V z →
      i ∉ markedRootPartitionCutIndices N
        (markedTransportedRatioAllCuts z w (markedRawGoodArcLevels e x a d₀ Y (64*H))) →
      ∀ p ∈ markedRootPartitionCell N i,∀ q ∈ markedRootPartitionCell N i,
      MarkedRootPhysicalGoodBox e x a d₀ Y U V z w p ↔
        MarkedRootPhysicalGoodBox e x a d₀ Y U V z w q := by
  filter_upwards [markedRootArc_actual_widths_eventually e he] with x hx
  intro M a d₀ Y U V H hY hU hV hH z w hdet hw N hN i hface hcut p hp q hq
  exact markedRootPhysicalGoodBox_cell_constancy e x a d₀ Y U V H hU hV hH z w hdet hw N hN i
    hface hcut ((hx.2 Y hY).2.le.trans (by norm_num))
    (fun j => (hx.1 j).2.le.trans (by norm_num)) p q hp hq

end ArtinMatthews
