module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuationBase
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAway
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaHighStrip
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.ODE.Gronwall
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Polynomial horizontal Gamma ratios from the proved actual mixed
Gamma logarithmic derivative estimate. This is the Gamma input for a
conductor-uniform Phragmén--Lindelöf convexity bound. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Set Complex
open scoped Classical BigOperators
noncomputable section

theorem horizontal_ratio_le_exp_logDeriv_bound
    {f : ℂ → ℂ} {a b t C : ℝ} (hab : a ≤ b)
    (hfd : ∀ x ∈ Icc a b, DifferentiableAt ℂ f ((x : ℂ)+(t : ℂ)*I))
    (hnz : ∀ x ∈ Icc a b, f ((x : ℂ)+(t : ℂ)*I) ≠ 0)
    (hbound : ∀ x ∈ Icc a b, ‖logDeriv f ((x : ℂ)+(t : ℂ)*I)‖ ≤ C) :
    ‖f ((b : ℂ)+(t : ℂ)*I) * (f ((a : ℂ)+(t : ℂ)*I))⁻¹‖ ≤
      Real.exp (C*(b-a)) := by
  let F : ℝ → ℂ := fun x => f ((x : ℂ)+(t : ℂ)*I)
  let F' : ℝ → ℂ := fun x => deriv f ((x : ℂ)+(t : ℂ)*I)
  have hd (x : ℝ) (hx : x ∈ Icc a b) : HasDerivAt F (F' x) x := by
    have H := ((hfd x hx).hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ)*I))).comp_ofReal
    simpa only [F,F',Function.comp_def,id_eq,mul_one] using H
  have hc : ContinuousOn F (Icc a b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hbnd (x : ℝ) (hx : x ∈ Ico a b) : ‖F' x‖ ≤ C*‖F x‖+0 := by
    have hx' : x ∈ Icc a b := ⟨hx.1,hx.2.le⟩
    have he : F' x = logDeriv f ((x : ℂ)+(t : ℂ)*I)*F x := by
      dsimp [F,F']
      rw [logDeriv_apply,div_mul_cancel₀ _ (hnz x hx')]
    rw [he,norm_mul,add_zero]
    exact mul_le_mul_of_nonneg_right (hbound x hx') (norm_nonneg _)
  have H := norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun x hx => (hd x ⟨hx.1,hx.2.le⟩).hasDerivWithinAt) (le_refl ‖F a‖) hbnd b ⟨hab,le_rfl⟩
  rw [gronwallBound_ε0] at H
  rw [norm_mul,norm_inv,← div_eq_mul_inv]
  apply (div_le_iff₀ (norm_pos_iff.mpr (hnz a ⟨le_rfl,hab⟩))).mpr
  simpa only [F,mul_comm] using H

theorem mixedGammaFactor_ne_zero_of_im_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : s.im ≠ 0) :
    mixedGammaFactor K s ≠ 0 := by
  change (∏ w : InfinitePlace K, mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  exact mixedGammaAtom_ne_zero_away (mixedGammaArgument_away_of_im_ne_zero K hs w)

theorem mixedGammaFactor_differentiableAt_of_im_ne_zero
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (mixedGammaFactor K) s := by
  change DifferentiableAt ℂ (fun z : ℂ =>
    ∏ w : InfinitePlace K, mixedGammaAtom ((InfinitePlace.mult w : ℂ)*z/2)) s
  apply DifferentiableAt.fun_finsetProd
  intro w _
  exact (mixedGammaAtom_differentiableAt_away
    (mixedGammaArgument_away_of_im_ne_zero K hs w)).comp s
      (show DifferentiableAt ℂ (fun z : ℂ => (InfinitePlace.mult w : ℂ)*z/2) s from by fun_prop)

theorem exists_mixedGammaFactor_horizontal_ratio_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type*) [Field K] [NumberField K],
      ∀ t : ℝ, 1 ≤ |t| →
        ‖mixedGammaFactor K ((5/4 : ℂ)+(t : ℂ)*I) *
          mixedInverseGammaFactor K ((-1/4 : ℂ)+(t : ℂ)*I)‖ ≤
            (|t|+2)^(B*(Module.finrank ℚ K : ℝ)) := by
  obtain ⟨B,hB,hbound⟩ := exists_mixedGammaFactor_high_strip_logarithmic_bound
  refine ⟨2*B,by positivity,?_⟩
  intro K _ _ t ht
  have htz : t ≠ 0 := by intro h; norm_num [h] at ht
  have him (x : ℝ) : ((x : ℂ)+(t : ℂ)*I).im ≠ 0 := by simpa using htz
  have H := horizontal_ratio_le_exp_logDeriv_bound
    (f := mixedGammaFactor K) (a := -1/4) (b := 5/4) (t := t)
    (C := B*(Module.finrank ℚ K : ℝ)*Real.log (|t|+2)) (by norm_num)
    (fun x _ => mixedGammaFactor_differentiableAt_of_im_ne_zero K (him x))
    (fun x _ => mixedGammaFactor_ne_zero_of_im_ne_zero K (him x))
    (fun x hx => by
      have H := hbound K ((x : ℂ)+(t : ℂ)*I)
        (by simpa using (show -(1/2 : ℝ) ≤ x by linarith [hx.1]))
        (by simpa using (show x ≤ 2 by linarith [hx.2])) (by simpa using ht)
      simpa using H)
  push_cast at H
  change ‖mixedGammaFactor K ((5/4 : ℂ)+(t : ℂ)*I) *
    (mixedGammaFactor K ((-1/4 : ℂ)+(t : ℂ)*I))⁻¹‖ ≤ _
  apply H.trans
  rw [Real.rpow_def_of_pos (by linarith [abs_nonneg t])]
  apply Real.exp_le_exp.mpr
  have hn : 0 ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have hl : 0 ≤ Real.log (|t|+2) := Real.log_nonneg (by linarith [abs_nonneg t])
  nlinarith [mul_nonneg (mul_nonneg hB.le hn) hl]

end
end ArtinMatthews.VaryingKummerAnalytic
