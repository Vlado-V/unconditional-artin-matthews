module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
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

/-! Main-term control for the exact reciprocal-coordinate interval sandwiches. -/
namespace ArtinMatthews
open scoped BigOperators

noncomputable def fixedURootReciprocalOuterWidth (α β ε : ℝ) : ℝ :=
  (1-α)-max 0 (1-β-ε)

noncomputable def fixedURootReciprocalInnerWidth (α β ε : ℝ) : ℝ :=
  max (1-β) (1-α-ε)-(1-β)

/-- The exact clipped reciprocal intervals change the original width by at
most the reciprocal-coordinate displacement. -/
theorem fixedURoot_reciprocal_width_bounds {α β ε : ℝ}
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1) (hε : 0 ≤ ε) :
    0 ≤ fixedURootReciprocalInnerWidth α β ε ∧
    fixedURootReciprocalInnerWidth α β ε ≤ β-α ∧
    β-α ≤ fixedURootReciprocalOuterWidth α β ε ∧
    fixedURootReciprocalOuterWidth α β ε ≤ 1 ∧
    (β-α)-fixedURootReciprocalInnerWidth α β ε ≤ ε ∧
    fixedURootReciprocalOuterWidth α β ε-(β-α) ≤ ε := by
  simp only [fixedURootReciprocalInnerWidth,fixedURootReciprocalOuterWidth,max_def]
  split_ifs <;> refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> linarith

/-- The actual special-linear root density lies between zero and one. -/
theorem fixedURoot_normalized_density_bounds {S : ℕ} (hS : Squarefree S) :
    0 ≤ 1 / ((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) ∧
    1 / ((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) ≤ 1 := by
  let : NeZero S := ⟨hS.ne_zero⟩
  have hcard : (1 : ℝ) ≤ (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) from Nat.card_pos)
  have hz : (riemannZeta 2).re = Real.pi^2/6 := by
    rw [riemannZeta_two,← Complex.ofReal_pow]
    norm_num [pow_two,Complex.mul_re]
  have hz1 : 1 ≤ (riemannZeta 2).re := by rw [hz]; nlinarith [Real.pi_gt_three]
  have hden : 1 ≤ (riemannZeta 2).re *
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by nlinarith
  constructor
  · positivity
  · exact (div_le_one (by linarith)).mpr hden

/-- Moving the normalized root-box width by `ε` costs at most `area*ε`. -/
theorem fixedURoot_interval_mass_shift {S : ℕ} (hS : Squarefree S)
    {W a b ε : ℝ} (hW : 0 ≤ W) (hab : |a-b| ≤ ε) :
    |W*a/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) -
      W*b/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤ W*ε := by
  obtain ⟨hq0,hq1⟩ := fixedURoot_normalized_density_bounds hS
  have he : W*a/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) -
      W*b/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) =
      (W*(a-b))*(1/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))) := by ring
  rw [he,abs_mul,abs_mul,abs_of_nonneg hW,abs_of_nonneg hq0]
  calc
    _ ≤ (W*ε)*1 := mul_le_mul (mul_le_mul_of_nonneg_left hab hW) hq1 hq0
      (mul_nonneg hW ((abs_nonneg _).trans hab))
    _ = _ := mul_one _

/-- At the actual reciprocal displacement `1/(A*C)`, the root main-mass
change is bounded by an absolute constant in the source coordinate ranges. -/
theorem fixedURoot_reciprocal_mass_shift_le {S : ℕ} (hS : Squarefree S)
    {A B C D a b : ℝ} (hA : 0 < A) (hC : 0 < C) (hAB : A ≤ B)
    (hB : B ≤ 16*A) (hCD : C ≤ D) (hY : D-C ≤ C)
    (hab : |a-b| ≤ 1/(A*C)) :
    |((B-A)*(D-C))*a/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) -
      ((B-A)*(D-C))*b/((riemannZeta 2).re *
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤ 16 := by
  have hW : 0 ≤ (B-A)*(D-C) := mul_nonneg (sub_nonneg.mpr hAB) (sub_nonneg.mpr hCD)
  have hh := fixedURoot_interval_mass_shift hS hW hab
  refine hh.trans ?_
  have harea : (B-A)*(D-C) ≤ 16*(A*C) := by
    have hm := mul_le_mul (show B-A ≤ 16*A by linarith) hY
      (sub_nonneg.mpr hCD) (by positivity : 0 ≤ 16*A)
    nlinarith
  rw [one_div,← div_eq_mul_inv]
  exact (div_le_iff₀ (mul_pos hA hC)).mpr harea

end ArtinMatthews
