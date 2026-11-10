module

public import ArtinMatthews.CubicThetaShiftedCorrelation
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! The integer-indexed paper sum agrees with the natural-indexed correlation,
because its source is supported on a strictly positive interval. -/

noncomputable section
open Set OAI
namespace ArtinMatthews

def thetaShiftedIntegerTerm (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  idealThetaCoeff χ ((m1 : ℤ)*n+1).toNat * idealThetaCoeff χ ((m2 : ℤ)*n+1).toNat * g n

theorem thetaShiftedIntegerTerm_nat (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (g : ℝ → ℂ) (n : ℕ) :
    thetaShiftedIntegerTerm χ m1 m2 g n =
      idealThetaCoeff χ (m1*n+1) * idealThetaCoeff χ (m2*n+1) * g n := by
  simp only [thetaShiftedIntegerTerm, ← Nat.cast_mul, ← Nat.cast_add_one,
    Int.toNat_natCast, Int.cast_natCast]

theorem thetaShiftedIntegerCorrelation_eq_nat (χ : SevenEighths.HeckeFamily.Character)
    (m1 m2 : ℕ) (T : ℝ) (hT : 0 < T) (g : ℝ → ℂ)
    (hg : Function.support g ⊆ Icc T (2*T)) :
    Summable (thetaShiftedIntegerTerm χ m1 m2 g) ∧
      (∑' n : ℤ, thetaShiftedIntegerTerm χ m1 m2 g n) = thetaShiftedCorrelation χ m1 m2 g := by
  have hpos : Summable (fun n : ℕ => thetaShiftedIntegerTerm χ m1 m2 g n) := by
    simpa only [thetaShiftedIntegerTerm_nat] using thetaShiftedCorrelation_summable χ m1 m2 T g hg
  have hzero (n : ℕ) : thetaShiftedIntegerTerm χ m1 m2 g (-(n+1)) = 0 := by
    have hz : g ((-(n+1) : ℤ) : ℝ) = 0 := by
      by_contra hn
      have hp := (hg hn).1
      push_cast at hp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    simp only [thetaShiftedIntegerTerm, hz, mul_zero]
  have hneg : Summable (fun n : ℕ => thetaShiftedIntegerTerm χ m1 m2 g (-(n+1))) := by
    simp only [hzero, summable_zero]
  refine ⟨hpos.of_nat_of_neg_add_one hneg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  simp only [hzero, tsum_zero, add_zero, thetaShiftedIntegerTerm_nat, thetaShiftedCorrelation]

end ArtinMatthews
