module

public import ArtinMatthews.PrincipalAngularResidue
public import ArtinMatthews.SourceRayAbsoluteBounds
public import ArtinMatthews.PrincipalDedekindAbsoluteContour
public import ArtinMatthews.PrincipalDedekindProbeGrowth
public import ArtinMatthews.ProbeIdealSourceRegions
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

/-! Bounds for the literal finite-S Dedekind factor in the source Euler
continuation. The finite correction stays visible on both sides of the
pole, including at the two principal remainder lines. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (ProbePrime F))

theorem sourceExteriorZetaEulerFactor_norm_le {s : ℂ} (hs : 0 ≤ s.re) :
    ‖principalZetaEulerFactor S s‖ ≤ (2 : ℝ)^S.card := by
  rw [principalZetaEulerFactor, norm_prod]
  calc
    _ ≤ ∏ _P ∈ S, (2 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro P _
      have hN := probeIdealPrime_norm_gt_one F P
      have hp : ‖(Ideal.absNorm P.asIdeal : ℂ)^(-s)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith), Complex.neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos hN.le (neg_nonpos.mpr hs)
      exact (norm_sub_le (1 : ℂ) _).trans (by rw [norm_one]; linarith)
    _ = _ := by simp

theorem sourceExteriorZeta_norm_le_right {a : ℝ} (ha : 1 < a) {s : ℂ} (hs : a ≤ s.re) :
    ‖principalExteriorZeta S s‖ ≤ sourceRayAbsoluteEulerBound F a * (2 : ℝ)^S.card := by
  have hζ : ‖mixedDedekindZeta F s‖ ≤ sourceRayAbsoluteEulerBound F a := by
    rw [mixedDedekindZeta_eq F (ha.trans_le hs), ← exp_dedekindEulerLog_eq_dedekindZeta F (ha.trans_le hs),
      Complex.norm_exp, sourceRayAbsoluteEulerBound]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (principalEulerLog_norm_le_right F ha hs))
  rw [principalExteriorZeta, norm_mul]
  exact mul_le_mul hζ (sourceExteriorZetaEulerFactor_norm_le F S (by linarith)) (norm_nonneg _)
    (sourceRayAbsoluteEulerBound_pos F a).le

theorem sourceExteriorZeta_scaled_norm_le_right {a : ℝ} (ha : 1/6 < a) {z : ℂ} (hz : a ≤ z.re) :
    ‖principalExteriorZeta S (6*z)‖ ≤ sourceRayAbsoluteEulerBound F (6*a) * (2 : ℝ)^S.card := by
  apply sourceExteriorZeta_norm_le_right F S (by linarith)
  have he : ((6 : ℂ)*z).re = 6*z.re := by norm_num [Complex.mul_re]
  rw [he]
  linarith

theorem exists_sourceExteriorZeta_height_bound_away_pole :
    ∃ (C : ℝ) (m : ℕ), 0 < C ∧ ∀ δ : ℝ, 0 < δ → ∀ s : ℂ, 0 ≤ s.re → δ ≤ ‖s-1‖ →
      ‖principalExteriorZeta S s‖ ≤
        (C/δ + sourceRayAbsoluteEulerBound F (5/4))*(2 : ℝ)^S.card*(|s.im|+2)^m := by
  obtain ⟨C, m, hC, hbound⟩ := exists_mixedDedekindZeta_strip_bound_away_pole F
  refine ⟨C, m, hC, ?_⟩
  intro δ hδ s hs hp
  let B := sourceRayAbsoluteEulerBound F (5/4)
  have hB : 0 < B := sourceRayAbsoluteEulerBound_pos F _
  have hh : 1 ≤ (|s.im|+2)^m := one_le_pow₀ (by linarith [abs_nonneg s.im])
  by_cases hw : s.re ≤ 5/4
  · rw [principalExteriorZeta, norm_mul]
    calc
      _ ≤ ((C/δ)*(|s.im|+2)^m)*(2 : ℝ)^S.card :=
        mul_le_mul (hbound δ hδ s (by linarith) hw hp) (sourceExteriorZetaEulerFactor_norm_le F S hs)
          (norm_nonneg _) (by positivity)
      _ = (C/δ)*(2 : ℝ)^S.card*(|s.im|+2)^m := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le)
        (by positivity)) (by positivity)
  · have h := sourceExteriorZeta_norm_le_right F S (by norm_num : (1:ℝ) < 5/4)
        (le_of_lt (lt_of_not_ge hw))
    exact h.trans ((mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (div_nonneg hC.le hδ.le))
      (by positivity)).trans (le_mul_of_one_le_right (by positivity) hh))

end
end ArtinMatthews.SourceEulerAssembly
