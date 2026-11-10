module

public import ArtinMatthews.MarkedTypeIITransport
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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

/-! Exact finite level cuts for the actual transported complement ratio.
No arbitrary boundary-count assumption is used. -/

noncomputable section
namespace ArtinMatthews

def markedTransportedRatioCut (z w : Fin 2 → ℝ) (a : ℝ) : ℝ :=
  (a*z 0-w 0)/(w 1-a*z 1)

def markedTransportedRatioCuts (z w : Fin 2 → ℝ) (levels : Finset ℝ) : Finset ℝ :=
  levels.image (markedTransportedRatioCut z w)

theorem markedTransportedRatio_level_coefficient (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) {r a : ℝ}
    (hz : markedTau r z ≠ 0) (ha : markedTransportedRatio r z w = a) :
    w 1-a*z 1 ≠ 0 := by
  have he : markedTau r w = a*markedTau r z := (div_eq_iff hz).mp ha
  unfold markedTau at he
  intro hzero
  have hw1 : w 1 = a*z 1 := sub_eq_zero.mp hzero
  rw [hw1] at he
  have hw0 : w 0 = a*z 0 := by linear_combination he
  unfold markedVectorDet at hdet
  rw [hw1,hw0] at hdet
  nlinarith

theorem markedTransportedRatio_eq_cut (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) {r a : ℝ}
    (hz : markedTau r z ≠ 0) (ha : markedTransportedRatio r z w = a) :
    r = markedTransportedRatioCut z w a := by
  have hc := markedTransportedRatio_level_coefficient z w hdet hz ha
  have he : markedTau r w = a*markedTau r z := (div_eq_iff hz).mp ha
  unfold markedTau at he
  apply (eq_div_iff hc).mpr
  nlinarith

theorem markedTransportedRatio_mem_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r : ℝ}
    (hz : markedTau r z ≠ 0) (hr : markedTransportedRatio r z w ∈ levels) :
    r ∈ markedTransportedRatioCuts z w levels := by
  apply Finset.mem_image.mpr
  exact ⟨markedTransportedRatio r z w,hr,(markedTransportedRatio_eq_cut z w hdet hz rfl).symm⟩

theorem markedTransportedRatioCuts_card_le (z w : Fin 2 → ℝ) (levels : Finset ℝ) :
    (markedTransportedRatioCuts z w levels).card ≤ levels.card := Finset.card_image_le

theorem markedTransportedRatio_ne_levels_off_cuts (z w : Fin 2 → ℝ)
    (hdet : markedVectorDet z w = 1) (levels : Finset ℝ) {r : ℝ}
    (hz : markedTau r z ≠ 0) (hr : r ∉ markedTransportedRatioCuts z w levels) :
    markedTransportedRatio r z w ∉ levels :=
  fun h => hr (markedTransportedRatio_mem_cuts z w hdet levels hz h)

end ArtinMatthews
