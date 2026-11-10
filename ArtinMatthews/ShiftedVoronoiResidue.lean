module

public import ArtinMatthews.ShiftedVoronoiCharacter
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import ArtinMatthews.ShiftedVoronoiDualSummation
public import ArtinMatthews.ShiftedVoronoiSourceSummation
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
# Voronoi summation with the actual residue-class inverse

A Bezout cusp matrix is constructed from a unit modulo q. Its lower-right entry
is proved to be that unit's inverse; the quadratic character of the numerator
is retained. Source and dual convergence follow from the proved analytic sums.
-/

noncomputable section
open Complex UpperHalfPlane Set
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

/-- An additive twist of the actual cusp coefficients by a residue class. -/
def cuspResidueCoeff {F : Type*} [FunLike F ℍ ℂ] (f : F) (q : ℕ) [NeZero q]
    (a : ZMod q) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n * ZMod.stdAddChar (a * (n : ZMod q))

/-- The residue character is exactly the rational additive phase, without any
choice of representative in the statement of the coefficient. -/
theorem cuspResidueCoeff_intCast {F : Type*} [FunLike F ℍ ℂ] (f : F)
    (q : ℕ) [NeZero q] (a : ℤ) (n : ℕ) :
    cuspResidueCoeff f q (a : ZMod q) n = cuspAdditiveCoeff f ((a : ℝ) / q) n := by
  unfold cuspResidueCoeff cuspAdditiveCoeff
  have hc := ZMod.stdAddChar_coe (N := q) (a * n)
  simp only [Int.cast_mul, Int.cast_natCast] at hc
  rw [hc]
  congr 2
  push_cast
  ring

/-- A canonical real lift used solely to apply the analytic summability results. -/
theorem cuspResidueCoeff_eq_val {F : Type*} [FunLike F ℍ ℂ] (f : F)
    (q : ℕ) [NeZero q] (a : ZMod q) (n : ℕ) :
    cuspResidueCoeff f q a n = cuspAdditiveCoeff f ((a.val : ℝ) / q) n := by
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using
    cuspResidueCoeff_intCast f q (a.val : ℤ) n

/-- Actual convergence of a smooth compact source twist. -/
theorem weightOne_source_residue_summable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (q : ℕ) [NeZero q] (c : ZMod q)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) :
    Summable (fun n : ℕ ↦ cuspResidueCoeff f q c n * H n) := by
  simp_rw [cuspResidueCoeff_eq_val]
  simpa only [div_one] using (weightOne_source_sum_mellin f hperiod ((c.val : ℝ) / q)
    H hH a b ha hHs 2 1 (by norm_num) (by norm_num)).summable

/-- Actual convergence of the Bessel-transformed twist at scale q². -/
theorem weightOne_dual_residue_summable
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (f : CuspForm Γ 1) (hperiod : (1 : ℝ) ∈ Γ.strictPeriods)
    (q : ℕ) [NeZero q] (c : ZMod q)
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (a b : ℝ) (ha : 0 < a)
    (hHs : Function.support H ⊆ Icc a b) :
    Summable (fun n : ℕ ↦ cuspResidueCoeff f q c n *
      weightOneBesselTransform H ((n : ℝ) / (q : ℝ) ^ 2)) := by
  have hc : HasCompactSupport H := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hHs
  let W := hc.toSchwartzMap hH
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  simp_rw [cuspResidueCoeff_eq_val]
  exact (weightOne_dual_sum_mellin f hperiod ((c.val : ℝ) / q) W a b ha hHs 2
    ((q : ℝ) ^ 2) (by norm_num) (by positivity)).summable

/-- The exact rational Voronoi formula in residue notation: the dual phase is
−a⁻¹, and its prefactor is ψ(a)/q. No cusp matrix or modular membership is assumed. -/
theorem weightOne_voronoi_residue
    (N : ℕ) [NeZero N] (hN : 3 ∣ N) (f : CuspForm (cubicThetaKernel N) 1)
    (q : ℕ) [NeZero q] (hlevel : N ∣ q) (a : ℤ) (haq : IsUnit (a : ZMod q))
    (H : ℝ → ℂ) (hH : ContDiff ℝ ∞ H) (u v : ℝ) (hu : 0 < u)
    (hHs : Function.support H ⊆ Icc u v) :
    (∑' n : ℕ, cuspResidueCoeff f q (a : ZMod q) n * H n) =
      (cubicThetaNebentypus a / (q : ℂ)) * ∑' n : ℕ,
        cuspResidueCoeff f q (-(a : ZMod q)⁻¹) n *
          weightOneBesselTransform H ((n : ℝ) / (q : ℝ) ^ 2) := by
  have hcop := ((ZMod.coe_int_isUnit_iff_isCoprime a q).mp haq).symm
  obtain ⟨γ, hγa, hγq⟩ := hcop.exists_SL2_col 0
  have hdet : a * γ 1 1 - γ 0 1 * (q : ℤ) = 1 := by
    simpa only [Matrix.det_fin_two, hγa, hγq] using γ.det_coe
  have hdetq : (a : ZMod q) * (γ 1 1 : ZMod q) = 1 := by
    have := congrArg (fun z : ℤ ↦ (z : ZMod q)) hdet
    simpa using this
  have hinv : (γ 1 1 : ZMod q) = (a : ZMod q)⁻¹ :=
    (ZMod.inv_eq_of_mul_eq_one q _ _ hdetq).symm
  have hq3 : (q : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (hN.trans hlevel)
  have hdet3 : (a : ZMod 3) * (γ 1 1 : ZMod 3) = 1 := by
    have := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hdet
    simpa [hq3] using this
  have heq : ∀ x y : ZMod 3, x * y = 1 → quadraticChar (ZMod 3) x = quadraticChar (ZMod 3) y := by decide
  have hψ : cubicThetaNebentypus (γ 1 1) = cubicThetaNebentypus a := by
    unfold cubicThetaNebentypus
    rw [heq _ _ hdet3]
  have hγlevel : (N : ℤ) ∣ γ 1 0 := by rw [hγq]; exact_mod_cast hlevel
  have hγnz : γ 1 0 ≠ 0 := by rw [hγq]; exact_mod_cast NeZero.ne q
  have hv := weightOne_voronoi_cubicNebentypus N hN f γ hγlevel hγnz H hH u v hu hHs
  rw [hγa, hγq, hψ] at hv
  simp only [Int.cast_natCast] at hv
  simp_rw [cuspResidueCoeff_intCast] 
  convert hv using 1
  congr 1
  apply tsum_congr
  intro n
  congr 1
  have hd := cuspResidueCoeff_intCast f q (-(γ 1 1)) n
  simpa only [Int.cast_neg, hinv, Complex.ofReal_neg, neg_div] using hd

end ArtinMatthews
