module

public import ArtinMatthews.ShiftedVoronoiCoefficientSeries
public import ArtinMatthews.ShiftedVoronoiReflection
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
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


set_option backward.privateInPublic true
@[expose] public section

/-!
# Mellin representation of actual additive-twist coefficient series

The exponential expansion follows from the actual q-expansion. Absolute
convergence then permits termwise integration in the half-plane `re s > 1`.
-/

noncomputable section
open Complex UpperHalfPlane MeasureTheory Set
open scoped MatrixGroups

namespace ArtinMatthews

/-- The convergent exponential expansion on a vertical line. -/
theorem cuspVerticalRestriction_hasSum
    {Γ : Subgroup (GL (Fin 2) ℝ)} (f : CuspForm Γ 1)
    (hperiod : (1 : ℝ) ∈ Γ.strictPeriods) (x y : ℝ) (hy : 0 < y) :
    HasSum (fun n : ℕ ↦ cuspAdditiveCoeff f x n *
      Real.exp (-(2 * Real.pi * n) * y)) (cuspVerticalRestriction f x y) := by
  let : Fact (IsCusp .infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods (by norm_num) hperiod⟩
  have h := ModularForm.hasSum_qExpansion f (by norm_num) hperiod
    (cuspVerticalPoint x y hy)
  convert h using 1
  · funext n
    simp only [cuspAdditiveCoeff, Function.Periodic.qParam, coe_cuspVerticalPoint,
      Complex.ofReal_one, div_one, ← Complex.exp_nat_mul, ← mul_assoc,
      Complex.ofReal_exp]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp only [cuspVerticalRestriction, dite_eq_left hy]

/-- Termwise Mellin integration, with no coefficient summability assumed:
it is discharged from the actual weight-one cusp-form bound. -/
theorem weightOne_additiveCoeff_mellin
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (x : ℝ) (s : ℂ) (hs : 1 < s.re) :
    mellin (cuspVerticalRestriction f x) s =
      ((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s *
        LSeries (cuspAdditiveCoeff f x) s := by
  let a := cuspAdditiveCoeff f x
  have ha0 : a 0 = 0 := cuspAdditiveCoeff_zero f hperiod x
  have hlsum := weightOne_additiveCoeff_LSeriesSummable f hperiod x s hs
  have hsum : Summable (fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ s.re) := by
    have heq : (fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ s.re) =
        fun n : ℕ ↦ ‖LSeries.term a s n‖ := by
      funext n
      rw [LSeries.norm_term_eq]
      by_cases hn : n = 0
      · subst n
        simp [ha0]
      · simp [hn]
    rw [heq]
    exact hlsum.norm
  have hp (n : ℕ) : a n = 0 ∨ 0 < 2 * Real.pi * n := by
    rcases n with _ | n
    · exact Or.inl ha0
    · exact Or.inr (by positivity)
  have hscaled : Summable (fun n : ℕ ↦ ‖a n‖ / (2 * Real.pi * n) ^ s.re) := by
    convert hsum.mul_left ((2 * Real.pi) ^ s.re)⁻¹ using 1
    funext n
    rw [Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi) (Nat.cast_nonneg n)]
    ring
  have hm := hasSum_mellin hp (by linarith : 0 < s.re)
    (fun y hy ↦ cuspVerticalRestriction_hasSum f hperiod x y hy) hscaled
  have hterm (n : ℕ) : Complex.Gamma s * a n / (2 * Real.pi * n : ℝ) ^ s =
      (((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity : 0 ≤ 2 * Real.pi)
          (Nat.cast_nonneg n), Complex.cpow_neg]
      push_cast
      ring
  have hm' : HasSum (fun n : ℕ ↦
      (((2 * Real.pi : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * LSeries.term a s n)
        (mellin (cuspVerticalRestriction f x) s) := by
    simpa only [hterm] using hm
  exact hm'.unique (hlsum.hasSum.mul_left _)

end ArtinMatthews
