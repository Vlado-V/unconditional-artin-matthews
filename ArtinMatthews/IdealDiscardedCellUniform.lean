module

public import ArtinMatthews.IdealLogCellPartition
public import ArtinMatthews.IdealLogCellCount
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual discarded-cell mass is small uniformly over growing
finite slot carriers, using their source logarithmic cardinality bound. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

def idealDiscardedThresholdExponent (d H E : ℝ) : ℝ := d+H+2*E+5

theorem idealDiscardedCellMass_uniform (d H E C : ℝ)
    (hd : 0 ≤ d) (hH : 0 ≤ H) :
    ∀ᶠ L : ℝ in atTop, ∀ (I : Type u) [Fintype I] [DecidableEq I],
      ∀ P : I → Finset ℕ, (∀ i p, p ∈ P i → p.Prime) →
      (∀ i p, p ∈ P i → (p : ℝ) ≤ Real.exp (L^d)) →
      (Fintype.card I : ℝ) ≤ C*Real.log L →
      idealDiscardedCellMass P (L^(-H)) (L^(-idealDiscardedThresholdExponent d H E)) ≤
        L^(-2*E-2) := by
  filter_upwards [eventually_ge_atTop (max 2 C)] with L hlarge
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hCL : C ≤ L := (le_max_right _ _).trans hlarge
  intro I _ _ P hP hupper hcard
  have hc : (Fintype.card I : ℝ) ≤ L^2 := by
    calc
      _ ≤ C*Real.log L := hcard
      _ ≤ L*L := mul_le_mul hCL (Real.log_le_self hL.le) (Real.log_nonneg hL1) hL.le
      _ = _ := (pow_two _).symm
  have hcount : 1+(Fintype.card I : ℝ)*L^d/L^(-H) ≤ L^(d+H+3) := by
    calc
      _ ≤ 1+L^2*L^d/L^(-H) := by
        have hz := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hL.le d)) (Real.rpow_nonneg hL.le (-H))
        linarith
      _ = 1+L^(d+H+2) := by
        rw [← Real.rpow_two, ← Real.rpow_add hL, ← Real.rpow_sub hL]
        congr 2
        ring
      _ ≤ 2*L^(d+H+2) := by
        have hp := Real.one_le_rpow hL1 (show 0 ≤ d+H+2 by linarith)
        linarith
      _ ≤ L*L^(d+H+2) := mul_le_mul_of_nonneg_right hL2 (Real.rpow_nonneg hL.le _)
      _ = _ := by nth_rw 1 [← Real.rpow_one L]; rw [← Real.rpow_add hL]; congr 1; ring
  calc
    _ ≤ (1+(Fintype.card I : ℝ)*L^d/L^(-H))*L^(-idealDiscardedThresholdExponent d H E) :=
      idealDiscardedCellMass_source_le P hP (Real.rpow_nonneg hL.le _) (Real.rpow_pos_of_pos hL _)
        (Real.rpow_nonneg hL.le _) hupper
    _ ≤ L^(d+H+3)*L^(-idealDiscardedThresholdExponent d H E) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hL.le _)
    _ = _ := by
      rw [← Real.rpow_add hL]
      congr 1
      dsimp [idealDiscardedThresholdExponent]
      ring

end
end ArtinMatthews
