module

public import ArtinMatthews.IdealLogCellPartition
public import ArtinMatthews.IdealResidualFamily
public import ArtinMatthews.GiantComparisonCellGeometry
public import ArtinMatthews.IdealLogCellCount
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual selected bands, logarithmic cells and primitive characters
have a common logarithmic cost before the growing family is chosen. -/
namespace ArtinMatthews
open Filter Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

universe u

theorem giantComparisonCellCountBudget_eventually (m : ℕ) (C₀ d CQ Ch Cξ : ℝ)
    (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hCQ : 0 ≤ CQ) (hCh : 0 ≤ Ch) (hCξ : 0 ≤ Cξ) :
    ∃ Ecost : ℝ, 0 ≤ Ecost ∧ ∀ᶠ L : ℝ in atTop,
      ∀ {G : Type u} [Fintype G] [DecidableEq G] (P : G → Finset ℕ) {k : ℕ}
        (A B : Finset (G × Fin k)),
      (Fintype.card G : ℝ) ≤ C₀*Real.log L →
      (∀ g, (idealResidualFreeSlots A g).card ≤ m) →
      (∀ g, (idealResidualFreeSlots B g).card ≤ m) →
      (∀ g p, p ∈ P g → p.Prime) →
      (∀ g p, p ∈ P g → (p : ℝ) ≤ Real.exp (L^d)) →
      ∀ (Q : ℕ) (h ξ : ℝ), (Q : ℝ) ≤ L^CQ → 0 < h → L^(-Ch) ≤ h → L^(-Cξ) ≤ ξ →
      let PA := idealResidualBands P A
      let PB := idealResidualBands P B
      ((idealLogCells PA h).card : ℝ)*((idealLogCells PB h).card : ℝ)*
        (Fintype.card (IdealPrimitiveCharacters Q) : ℝ)^2*(ξ⁻¹)^2 ≤ L^Ecost := by
  let F := d+Ch+3
  let Ecost := 2*F+4*CQ+2*Cξ
  refine ⟨Ecost, by unfold Ecost F; positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ), eventually_ge_atTop ((m : ℝ)*C₀)] with L hL hLm
  intro G _ _ P k A B hG hA hB hP hupper Q h ξ hQ hh hhL hξ
  have hL₁ : 1 ≤ L := one_le_two.trans hL
  have hL₀ : 0 < L := zero_lt_one.trans_le hL₁
  have hinv (t z : ℝ) (hz : L^(-t) ≤ z) : z⁻¹ ≤ L^t := by
    simpa only [one_div, Real.rpow_neg hL₀.le, inv_inv] using
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL₀ (-t)) hz
  have hcells (U : Finset (G × Fin k)) (hU : ∀ g, (idealResidualFreeSlots U g).card ≤ m) :
      ((idealLogCells (idealResidualBands P U) h).card : ℝ) ≤ L^F := by
    have hslots : (Fintype.card (↥U) : ℝ) ≤ (m : ℝ)*(Fintype.card G : ℝ) := by
      exact_mod_cast giantComparisonSelected_card_le U m hU
    have hcard : (Fintype.card (↥U) : ℝ) ≤ L^(2 : ℝ) := by
      rw [Real.rpow_two]
      calc
        _ ≤ (m : ℝ)*(C₀*Real.log L) := hslots.trans (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg m))
        _ = ((m : ℝ)*C₀)*Real.log L := by ring
        _ ≤ L*L := mul_le_mul hLm ((Real.log_le_sub_one_of_pos hL₀).trans (by linarith))
          (Real.log_nonneg hL₁) hL₀.le
        _ = _ := by ring
    have hdiv : (Fintype.card (↥U) : ℝ)*L^d/h ≤ L^(2+d+Ch) := by
      rw [div_eq_mul_inv, Real.rpow_add hL₀ (2+d) Ch, Real.rpow_add hL₀ (2 : ℝ) d]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hL₀.le _))
        (hinv Ch h hhL) (inv_nonneg.mpr hh.le) (by positivity)
    have hone : 1 ≤ L^(2+d+Ch) := Real.one_le_rpow hL₁ (by positivity)
    calc
      _ ≤ 1+(Fintype.card (↥U) : ℝ)*L^d/h := idealLogCells_card_le (idealResidualBands P U)
        (fun i p hp => hP i.val.1 p hp) (Real.rpow_nonneg hL₀.le _) hh
        (fun i p hp => hupper i.val.1 p hp)
      _ ≤ 1+L^(2+d+Ch) := add_le_add_right hdiv 1
      _ ≤ 2*L^(2+d+Ch) := by linarith only [hone]
      _ ≤ L*L^(2+d+Ch) := mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hL₀.le _)
      _ = L^F := by
        rw [show F = 1+(2+d+Ch) by unfold F; ring,
          Real.rpow_add hL₀ (1 : ℝ) (2+d+Ch), Real.rpow_one]
  have hchar : (Fintype.card (IdealPrimitiveCharacters Q) : ℝ) ≤ L^(2*CQ) := by
    have hc : (Fintype.card (IdealPrimitiveCharacters Q) : ℝ) ≤ (Q : ℝ)^2 := by
      exact_mod_cast idealPrimitiveCharacters_card_le Q
    calc
      _ ≤ (L^CQ)^2 := hc.trans (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQ 2)
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL₀.le, mul_comm CQ 2]
  have hξ₀ : 0 < ξ := (Real.rpow_pos_of_pos hL₀ (-Cξ)).trans_le hξ
  dsimp only
  calc
    _ ≤ L^F*L^F*(L^(2*CQ))^2*(L^Cξ)^2 := by
      have hc := mul_le_mul (hcells A hA) (hcells B hB) (Nat.cast_nonneg _) (by positivity)
      have hχ := pow_le_pow_left₀ (Nat.cast_nonneg _) hchar 2
      have hI := pow_le_pow_left₀ (inv_nonneg.mpr hξ₀.le) (hinv Cξ ξ hξ) 2
      exact mul_le_mul (mul_le_mul hc hχ (sq_nonneg _) (by positivity)) hI (sq_nonneg _) (by positivity)
    _ = _ := by
      rw [← Real.rpow_two (L^(2*CQ)), ← Real.rpow_mul hL₀.le,
        ← Real.rpow_two (L^Cξ), ← Real.rpow_mul hL₀.le,
        ← Real.rpow_add hL₀, ← Real.rpow_add hL₀, ← Real.rpow_add hL₀]
      congr 1
      unfold Ecost
      ring

end
end ArtinMatthews
