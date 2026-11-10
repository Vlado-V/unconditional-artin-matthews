module

public import ArtinMatthews.IdealResidualFamily
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

/-! The full source family has a fixed exponential cost in the probe
count. The copied-list length does not occur in this bound. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealResidualPatterns_card_le {J : Type*} [DecidableEq J] {k : ℕ}
    (probes₁ probes₂ : Finset (J × Fin k)) :
    (idealResidualPatterns probes₁ probes₂).card ≤ 1+2^(probes₁.card+probes₂.card) := by
  have h₁ : (probes₁.powerset.erase ∅).card ≤ 2^probes₁.card :=
    card_erase_le.trans_eq (card_powerset probes₁)
  have h₂ : (probes₂.powerset.erase ∅).card ≤ 2^probes₂.card :=
    card_erase_le.trans_eq (card_powerset probes₂)
  unfold idealResidualPatterns
  calc
    _ ≤ ({none} : Finset (IdealResidualPattern J k)).card+
        ((probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).image some).card := card_union_le _ _
    _ ≤ 1+(probes₁.powerset.erase ∅ ×ˢ probes₂.powerset.erase ∅).card := by
      rw [card_singleton]
      exact Nat.add_le_add_left (card_image_le) 1
    _ ≤ 1+2^(probes₁.card+probes₂.card) := by
      rw [card_product,pow_add]
      exact Nat.add_le_add_left (Nat.mul_le_mul h₁ h₂) 1

theorem idealResidualCoefficient_total_cost {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) {k ell : ℕ} (probes₁ probes₂ : Finset (J × Fin k))
    (Q : ℕ) (h : ℝ) {ξ : ℝ} (hξ : 0 < ξ)
    (a b : IdealResidualPattern J k → MarkedPhysicalMarking P (k+ell))
    (aux : ∀ ν,GiantTwoSidedPatternAuxiliary P (idealResidualCopied ν)) :
    (∑ ν∈idealResidualPatterns probes₁ probes₂,‖idealResidualCoefficient P Q h ξ ν (a ν) (b ν) (aux ν)‖) ≤
      ((1+2^(probes₁.card+probes₂.card):ℕ):ℝ)*(1+((Q:ℝ)^2/ξ)^2) := by
  calc
    _ ≤ ∑ _ν∈idealResidualPatterns probes₁ probes₂,(1+((Q:ℝ)^2/ξ)^2) :=
      sum_le_sum fun ν _ => idealResidualCoefficient_norm P Q h hξ ν (a ν) (b ν) (aux ν)
    _ = ((idealResidualPatterns probes₁ probes₂).card:ℝ)*(1+((Q:ℝ)^2/ξ)^2) := by
      rw [sum_const,nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast idealResidualPatterns_card_le probes₁ probes₂) (by positivity)

end
end ArtinMatthews
