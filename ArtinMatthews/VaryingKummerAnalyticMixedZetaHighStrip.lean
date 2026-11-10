module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaZero
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaHighStrip
public import ArtinMatthews.VaryingKummerAnalyticMixedXiNormBound
public import ArtinMatthews.VaryingKummerAnalyticMixedZeroScale
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaFunctionalEquation
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

/-! Transfer of the full xi logarithmic-derivative bound to the actual
uncompleted Dedekind zeta throughout the horizontal contour strip. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex
noncomputable section
universe u

theorem exists_mixedDedekindZeta_high_strip_logDeriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type u) [Field K] [NumberField K], ∀ s : ℂ,
      -(1/2 : ℝ) ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      mixedCompletedDedekindXi K s ≠ 0 →
      ‖logDeriv (mixedDedekindZeta K) s‖ ≤
        ‖logDeriv (mixedCompletedDedekindXi K) s‖ +
          C*(Real.log |(discr K : ℝ)| +
            (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2)) := by
  obtain ⟨B,hB,hgamma⟩ := exists_mixedGammaFactor_high_strip_logarithmic_bound.{u}
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let A := 2/Real.log 2
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨B+A+2,by positivity,?_⟩
  intro K _ _ s hs hs' him hxi
  have hi : s.im ≠ 0 := by intro h; norm_num [h] at him
  have hs0 : s ≠ 0 := by intro h; apply hi; simp [h]
  have hs1 : s ≠ 1 := by intro h; apply hi; simp [h]
  have hinv : ‖(1 : ℂ)/s‖ ≤ 1 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (him.trans (Complex.abs_im_le_norm s))
    simpa using h
  have hinv' : ‖(1 : ℂ)/(s-1)‖ ≤ 1 := by
    have hn : 1 ≤ ‖s-1‖ := by
      have h := Complex.abs_im_le_norm (s-1)
      simp only [Complex.sub_im,Complex.one_im,sub_zero] at h
      exact him.trans h
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    simpa using h
  have hscale : ‖(Real.log (mixedDiscriminantScale K) : ℂ)‖ ≤
      Real.log |(discr K : ℝ)|/2 + (Module.finrank ℚ K : ℝ)*Real.log 2 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      mixedDiscriminantScale_log_abs_le_degree K
  have hγ := hgamma K s hs hs' him
  have hD := discr_log_nonneg K
  have hn : 1 ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hn0 : 0 ≤ (Module.finrank ℚ K : ℝ) := by positivity
  have hl : Real.log 2 ≤ Real.log (|s.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hl0 := hl2.le.trans hl
  have htwo : 2 ≤ A*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
    have hterm : Real.log 2 ≤ (Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by nlinarith
    have h := mul_le_mul_of_nonneg_left hterm hA.le
    dsimp [A] at h ⊢
    rw [div_mul_cancel₀ _ hl2.ne'] at h
    simpa only [mul_assoc] using h
  have hnl := mul_le_mul_of_nonneg_left hl hn0
  have hCD := mul_nonneg (show 0 ≤ B+A+3/2 by positivity) hD
  rw [mixedDedekindZeta_logDeriv_eq_continuation K hs0,
    mixedDedekindZetaContinuation_logDeriv K hs0 hs1 hxi
      (mixedGammaArgument_away_of_im_ne_zero K hi)]
  have h₁ := norm_sub_le (logDeriv (mixedCompletedDedekindXi K) s) (1/s)
  have h₂ := norm_sub_le (logDeriv (mixedCompletedDedekindXi K) s-1/s) (1/(s-1))
  have h₃ := norm_sub_le (logDeriv (mixedCompletedDedekindXi K) s-1/s-1/(s-1))
    (Real.log (mixedDiscriminantScale K) : ℂ)
  have h₄ := norm_sub_le (logDeriv (mixedCompletedDedekindXi K) s-1/s-1/(s-1)-
    (Real.log (mixedDiscriminantScale K) : ℂ)) (logDeriv (mixedGammaFactor K) s)
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
