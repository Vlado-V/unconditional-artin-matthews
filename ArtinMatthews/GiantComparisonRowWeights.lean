module

public import ArtinMatthews.GiantComparisonFreeMarking
public import ArtinMatthews.SourceComparisonFreeHit
public import ArtinMatthews.GiantComparisonStripKernel
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The row envelope keeps the right character in its endpoint
coefficient and bounds the remaining auxiliary character by one. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section

theorem giantComparisonOrderedFreeWeight_nonneg {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k : ℕ} (C : J → Finset (Fin k)) (ell w : ℕ)
    (hV : ∀ j, 0 < bandReciprocalMass (P j)) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ giantComparisonOrderedFreeWeight P C ell q w := by
  unfold giantComparisonOrderedFreeWeight giantComparisonQuotientDamping
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (giantTwoSidedPatternFreshMass_nonneg C ell hV)) (pow_nonneg hq _)

theorem giantComparisonPositionKernel_weight_norm_le {m : ℕ} [NeZero m]
    (x : ℝ) (Ψ : ℝ → ℂ) (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) (d w : ℕ) :
    ‖giantComparisonPositionKernel x Ψ χ F G d w‖*W w*W (w+d) ≤
      sourceComparisonFreeHitWeight Ψ (fun n => F n*(W n:ℂ))
        (fun n => (χ n*G n)*(W n:ℂ)) (x*(d:ℝ)) d w := by
  let B := sourceComparisonFreeHitWeight Ψ (fun n => F n*(W n:ℂ))
    (fun n => (χ n*G n)*(W n:ℂ)) (x*(d:ℝ)) d w
  have hB : 0 ≤ B := sourceComparisonFreeHitWeight_nonneg _ _ _ _ _ _
  calc
    _ = B*‖χ (d:ℕ)‖ := by
      simp only [B,giantComparisonPositionKernel,sourceComparisonFreeHitWeight,
        norm_mul,norm_div,Complex.norm_natCast,Complex.norm_conj,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (hW w),abs_of_nonneg (hW (w+d))]
      ring
    _ ≤ B := by simpa only [mul_one] using mul_le_mul_of_nonneg_left (χ.norm_le_one (d:ZMod m)) hB

end
end ArtinMatthews
