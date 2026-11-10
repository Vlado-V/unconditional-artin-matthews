module

public import ArtinMatthews.GiantSignedUniformBirthFrame
public import ArtinMatthews.GiantSignedSourceOmissionGain
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual address frame has a polynomial coefficient-count base
whose exponent is independent of the fixed copied dimension. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem giantSignedSourceBirthAddress_budget_eventually
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (M : ℕ) :
    ∀ᶠ x : ℝ in atTop, ∀ (B : Type*) [Fintype B],
      let L := Real.log x
      let n := giantTwoSidedSourceMomentLength x
      let R := giantSignedSourceMemoryLimit L
      (Fintype.card B : ℝ) ≤ C₀ * Real.log L →
      (((Fintype.card (GiantSignedUniformBirthAddress B M n R) : ℝ)^2 + 1)^2) ≤ L^(30 : ℕ) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 5 (max C₀ (M : ℝ))))] with x hx
  intro B _
  dsimp only
  intro hB
  let L := Real.log x
  let n := giantTwoSidedSourceMomentLength x
  let R := giantSignedSourceMemoryLimit L
  have hL5 : 5 ≤ L := (le_max_left _ _).trans hx
  have hL2 : 2 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hM : (M : ℝ) ≤ L := (le_max_right C₀ _).trans ((le_max_right 5 _).trans hx)
  have hC : C₀ ≤ L := (le_max_left _ (M : ℝ)).trans ((le_max_right 5 _).trans hx)
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL).trans (by linarith)
  have hcardB : (Fintype.card B : ℝ) ≤ L^2 := by
    exact hB.trans ((mul_le_mul hC hlog (Real.log_nonneg hL1) hL.le).trans_eq (by ring))
  have hlen : ((n+1 : ℕ) : ℝ) ≤ L^2 := by
    have hp := Real.rpow_le_rpow_of_exponent_le hL1 (show (13/25 : ℝ) ≤ 1 by norm_num)
    rw [Real.rpow_one] at hp
    have hn := giantTwoSidedSourceMomentLength_le (x := x) hL1
    change (n : ℝ) ≤ 4 * L ^ (13/25 : ℝ) at hn
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hL5 hL.le]
  have hcap : (R : ℝ) ≤ 2*L^2 := giantSignedSourceMemoryLimit_le hL1
  have hdim : ((M+R : ℕ) : ℝ) ≤ L^3 := by
    push_cast
    nlinarith only [hM, hcap, mul_le_mul_of_nonneg_right hL1 hL.le,
      mul_le_mul_of_nonneg_right hL5 (sq_nonneg L)]
  have hcard : (Fintype.card (GiantSignedUniformBirthAddress B M n R) : ℝ) ≤ L^(7 : ℕ) := by
    rw [giantSignedUniformBirthAddress_card]
    push_cast only [Nat.cast_mul]
    calc
      _ ≤ (L^2 * L^2) * L^3 := mul_le_mul
        (mul_le_mul hlen hcardB (Nat.cast_nonneg _) (sq_nonneg L)) hdim
        (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have h14 : 1 ≤ L^(14 : ℕ) := one_le_pow₀ hL1
  have hbase : (Fintype.card (GiantSignedUniformBirthAddress B M n R) : ℝ)^2 + 1 ≤ L^(15 : ℕ) := by
    calc
      _ ≤ (L^(7 : ℕ))^2 + 1 := add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2) le_rfl
      _ = L^(14 : ℕ) + 1 := by ring
      _ ≤ L * L^(14 : ℕ) := by
        have hh := mul_le_mul_of_nonneg_right hL2 (pow_nonneg hL.le (14 : ℕ))
        nlinarith only [h14, hh]
      _ = _ := by ring
  change ((Fintype.card (GiantSignedUniformBirthAddress B M n R) : ℝ)^2 + 1)^2 ≤ L^(30 : ℕ)
  exact (pow_le_pow_left₀ (by positivity) hbase 2).trans_eq (by ring)

end
end ArtinMatthews
