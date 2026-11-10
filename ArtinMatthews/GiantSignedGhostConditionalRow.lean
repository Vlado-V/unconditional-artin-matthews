module

public import ArtinMatthews.GiantSignedGhostSimultaneous
public import ArtinMatthews.GiantSignedGhostSectorMajorant
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! A uniform mass bound for the genuinely fresh tuple in each
fixed ghost sector is carried through the actual factorial sum. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {B : Type*} [Fintype B] {P : B → Finset ℕ}

def giantSignedGhostFiniteBatchMove (m : GiantSignedMemory P) {H : ℕ}
    (deleted : ∀ g, Finset (Fin (m.1 g))) (b : B → Fin (H+1))
    (born : ∀ g, Fin (b g).val → P g) : GiantSignedGhostMemoryMoves m :=
  fun g => ⟨deleted g, (b g).val, born g⟩

theorem giantSignedGhostConditionalRow_le (ν : ∀ g, P g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) {v mass F : ℝ} (hv : 0 < v) (hmass : 0 ≤ mass) (hF : 0 ≤ F)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (m : GiantSignedMemory P) (H : ℕ)
    (Gate : (b : B → Fin (H+1)) → (∀ g, Fin (b g).val → P g) → Prop)
    (hGate : ∀ b, (∑ born : ∀ g, Fin (b g).val → P g,
        if Gate b born then ∏ g, ∏ i, ν g (born g i) else 0) ≤ F * mass^(∑ g, (b g).val)) :
    (∑ deleted : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1), ∑ born : ∀ g, Fin (b g).val → P g,
        if Gate b born then
          let r := giantSignedGhostFiniteBatchMove m deleted b born
          ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ *
            v^(∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g)
        else 0) ≤
      F * (v^(∑ g, m.1 g) * ∏ g, Real.exp (‖C g‖ * mass * v)) := by
  classical
  let sector (g : B) (del : Finset (Fin (m.1 g))) (b : Fin (H+1)) :=
    giantSignedGhostSectorMajorant (A g) (C g) (D g) v
      (giantSignedMemoryGroupEquiv P m g) del b.val
  have hs (g : B) (d : Finset (Fin (m.1 g))) (b : Fin (H+1)) : 0 ≤ sector g d b :=
    giantSignedGhostSectorMajorant_nonneg (A g) (C g) (D g) hv.le
      (giantSignedMemoryGroupEquiv P m g) d b.val
  have hlocal (deleted : ∀ g, Finset (Fin (m.1 g))) (b : B → Fin (H+1)) :
      (∑ born : ∀ g, Fin (b g).val → P g,
        if Gate b born then
          let r := giantSignedGhostFiniteBatchMove m deleted b born
          ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ *
            v^(∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g)
        else 0) ≤ F * ∏ g, sector g (deleted g) (b g) * mass^(b g).val := by
    have he :
        (∑ born : ∀ g, Fin (b g).val → P g,
          if Gate b born then
            let r := giantSignedGhostFiniteBatchMove m deleted b born
            ‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ *
              v^(∑ g, (giantSignedGhostMemoryMoveTarget m r).1 g)
          else 0) =
        (∏ g, sector g (deleted g) (b g)) *
          ∑ born : ∀ g, Fin (b g).val → P g,
            if Gate b born then ∏ g, ∏ i, ν g (born g i) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro born _
      by_cases h : Gate b born
      · rw [ite_eq_left h, ite_eq_left h]
        exact giantSignedGhostMemoryMove_norm_degree ν hν A C D v m
          (giantSignedGhostFiniteBatchMove m deleted b born)
      · simp only [h, ite_false, mul_zero]
    rw [he]
    refine (mul_le_mul_of_nonneg_left (hGate b) (Finset.prod_nonneg (fun g _ => hs g _ _))).trans_eq ?_
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    ring
  have hbudget :
      (∑ deleted : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1),
        ∏ g, sector g (deleted g) (b g) * mass^(b g).val) ≤
      v^(∑ g, m.1 g) * ∏ g, Real.exp (‖C g‖ * mass * v) := by
    have he (deleted : ∀ g, Finset (Fin (m.1 g))) :
        (∑ b : B → Fin (H+1), ∏ g, sector g (deleted g) (b g) * mass^(b g).val) =
          ∏ g, ∑ b : Fin (H+1), sector g (deleted g) b * mass^b.val :=
      (Fintype.prod_sum (fun g (b : Fin (H+1)) => sector g (deleted g) b * mass^b.val)).symm
    calc
      _ = ∏ g, ∑ del : Finset (Fin (m.1 g)), ∑ b : Fin (H+1), sector g del b * mass^b.val := by
        simp only [he]
        exact (Fintype.prod_sum (fun g (del : Finset (Fin (m.1 g))) =>
          ∑ b : Fin (H+1), sector g del b * mass^b.val)).symm
      _ ≤ _ := by
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
        exact Finset.prod_le_prod₀
          (fun g _ => Finset.sum_nonneg (fun del _ => Finset.sum_nonneg
            (fun b _ => mul_nonneg (hs g del b) (pow_nonneg hmass _))))
          (fun g _ => giantSignedGhostSectorMajorant_sum_le (A g) (C g) (D g) hv hmass (hrow g)
            (giantSignedMemoryGroupEquiv P m g) H)
  calc
    _ ≤ ∑ deleted : ∀ g, Finset (Fin (m.1 g)), ∑ b : B → Fin (H+1),
        F * ∏ g, sector g (deleted g) (b g) * mass^(b g).val :=
      Finset.sum_le_sum (fun deleted _ => Finset.sum_le_sum (fun b _ => hlocal deleted b))
    _ ≤ _ := by
      simp only [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hbudget hF

end
end ArtinMatthews
