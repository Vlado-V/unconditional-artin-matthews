module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLogDeriv
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gaussian Gamma atom has logarithmic derivative psi(s)-log(pi). -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped Classical BigOperators
noncomputable section

theorem mixedGammaAtom_logDeriv_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv mixedGammaAtom s = Complex.digamma s - Complex.log (Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  let p : ℂ → ℂ := fun z => (Real.pi : ℂ)^(-z)
  have hpne : p s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hpi)
  have hp := ((hasDerivAt_id s).neg).const_cpow (Or.inl hpi)
  have hplog : logDeriv p s = -Complex.log (Real.pi : ℂ) := by
    rw [logDeriv_apply,
      show deriv p s = p s * Complex.log (Real.pi : ℂ) * (-1) from hp.deriv]
    field_simp
  have hgd : DifferentiableAt ℂ Complex.Gamma s := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hh := congrArg Complex.re hn
    simp only [Complex.neg_re, Complex.natCast_re] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have he : mixedGammaAtom = fun z => (1/2 : ℂ)*(p z*Complex.Gamma z) := by
    funext z
    dsimp [mixedGammaAtom,p]
    ring
  rw [he, logDeriv_const_mul s (1/2) (by norm_num),
    logDeriv_fun_mul (f := p) (g := Complex.Gamma) s hpne
      (Complex.Gamma_ne_zero_of_re_pos hs) hp.differentiableAt hgd, hplog]
  change -Complex.log (Real.pi : ℂ) + Complex.digamma s = _
  ring

theorem mixedGammaFactor_logDeriv_norm_le_of_bounds
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 0 < s.re) {B : ℝ}
    (hb : ∀ w : InfinitePlace K,
      ‖logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ ≤ B) :
    ‖logDeriv (mixedGammaFactor K) s‖ ≤ ((Module.finrank ℚ K : ℝ)/2)*B := by
  rw [mixedGammaFactor_logDeriv_eq K hs]
  calc
    _ ≤ ∑ w : InfinitePlace K, ‖((InfinitePlace.mult w : ℂ)/2) *
        logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ := norm_sum_le _ _
    _ ≤ ∑ w : InfinitePlace K, ((InfinitePlace.mult w : ℝ)/2)*B := by
      apply Finset.sum_le_sum
      intro w _
      have hn : ‖(InfinitePlace.mult w : ℂ)/2‖ = (InfinitePlace.mult w : ℝ)/2 := by simp
      rw [norm_mul, hn]
      exact mul_le_mul_of_nonneg_left (hb w) (by positivity)
    _ = _ := by
      rw [← Finset.sum_mul, ← Finset.sum_div]
      have he : (∑ w : InfinitePlace K, (InfinitePlace.mult w : ℝ)) =
          (Module.finrank ℚ K : ℝ) := by
        exact_mod_cast InfinitePlace.sum_mult_eq (K := K)
      rw [he]

end
end ArtinMatthews.VaryingKummerAnalytic
