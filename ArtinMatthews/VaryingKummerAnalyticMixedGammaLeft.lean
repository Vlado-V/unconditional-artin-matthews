module

public import ArtinMatthews.VaryingKummerAnalyticMixedGammaLogDeriv
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAtomLog
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaAway
public import ArtinMatthews.VaryingKummerAnalyticMixedGammaVertical
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! Uniform logarithmic Gamma bounds on the left contour Re(s)=-1/2.
Gamma recurrence shifts both real and complex place arguments into a
fixed positive strip, a fixed distance from every Gamma pole. -/
namespace ArtinMatthews.VaryingKummerAnalytic

open NumberField
open scoped Classical BigOperators
noncomputable section
universe u

lemma gamma_left_argument_away {z : ℂ}
    (hz : -(1/2 : ℝ) ≤ z.re) (hz' : z.re ≤ -(1/4 : ℝ)) :
    ∀ n : ℕ, z ≠ -(n : ℂ) := by
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re,Complex.natCast_re] at he
  by_cases h : n = 0
  · subst n
    norm_num at he
    linarith
  · have hh : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
    linarith

lemma mixedGammaAtom_logDeriv_recurrence {z : ℂ}
    (hz : -(1/2 : ℝ) ≤ z.re) (hz' : z.re ≤ -(1/4 : ℝ)) :
    logDeriv mixedGammaAtom z = logDeriv mixedGammaAtom (z+1) - 1/z := by
  have ha := gamma_left_argument_away hz hz'
  have hp : 0 < (z+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  rw [mixedGammaAtom_logDeriv_eq_away ha, mixedGammaAtom_logDeriv_eq hp,
    Complex.digamma_apply_add_one z ha]
  ring

theorem mixedGammaAtom_left_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, -(1/2 : ℝ) ≤ z.re → z.re ≤ -(1/4 : ℝ) →
      ‖logDeriv mixedGammaAtom z‖ ≤ B*Real.log (|z.im|+2) := by
  obtain ⟨C,hC,hbound⟩ := mixedGammaAtom_logarithmic_bound
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C+4/Real.log 2,by positivity,?_⟩
  intro z hz hz'
  have hp₀ : (1/2 : ℝ) ≤ (z+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hp₁ : (z+1).re ≤ 2 := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hb := hbound (z+1) hp₀ hp₁
  simp only [Complex.add_im,Complex.one_im,add_zero] at hb
  have hn : (1/4 : ℝ) ≤ ‖z‖ := by
    have hr := Complex.abs_re_le_norm z
    rw [abs_of_neg (by linarith : z.re < 0)] at hr
    linarith
  have hi : ‖(1 : ℂ)/z‖ ≤ 4 := by
    rw [norm_div,norm_one]
    have H := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/4) hn
    norm_num at H
    simpa only [one_div] using H
  have hl : Real.log 2 ≤ Real.log (|z.im|+2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
  have h4 : 4 ≤ (4/Real.log 2)*Real.log (|z.im|+2) := by
    have H := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 4/Real.log 2)
    rwa [div_mul_cancel₀ _ hlog2.ne'] at H
  rw [mixedGammaAtom_logDeriv_recurrence hz hz']
  calc
    _ ≤ ‖logDeriv mixedGammaAtom (z+1)‖ + ‖(1 : ℂ)/z‖ := norm_sub_le _ _
    _ ≤ C*Real.log (|z.im|+2) + 4 := add_le_add hb hi
    _ ≤ (C+4/Real.log 2)*Real.log (|z.im|+2) := by nlinarith

theorem exists_mixedGammaFactor_left_logarithmic_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (K : Type u) [Field K] [NumberField K],
      ∀ s : ℂ, s.re = -(1/2 : ℝ) →
        ‖logDeriv (mixedGammaFactor K) s‖ ≤
          B*(Module.finrank ℚ K : ℝ)*Real.log (|s.im|+2) := by
  obtain ⟨B,hB,hbound⟩ := mixedGammaAtom_left_logarithmic_bound
  refine ⟨B,hB,?_⟩
  intro K _ _ s hs
  have hm₀ (w : InfinitePlace K) : (0 : ℝ) ≤ InfinitePlace.mult w := Nat.cast_nonneg _
  have hm₁ (w : InfinitePlace K) : (1 : ℝ) ≤ InfinitePlace.mult w := InfinitePlace.one_le_mult
  have hm₂ (w : InfinitePlace K) : (InfinitePlace.mult w : ℝ) ≤ 2 := by
    unfold InfinitePlace.mult
    split_ifs <;> norm_num
  have hre (w : InfinitePlace K) :
      (((InfinitePlace.mult w : ℂ)*s/2).re) = -(InfinitePlace.mult w : ℝ)/4 := by
    simp [hs]
    ring
  have harg (w : InfinitePlace K) :
      -(1/2 : ℝ) ≤ (((InfinitePlace.mult w : ℂ)*s/2).re) ∧
      (((InfinitePlace.mult w : ℂ)*s/2).re) ≤ -(1/4 : ℝ) := by
    rw [hre]
    constructor <;> linarith [hm₁ w,hm₂ w]
  have ha (w : InfinitePlace K) : ∀ n : ℕ,
      (InfinitePlace.mult w : ℂ)*s/2 ≠ -(n : ℂ) :=
    gamma_left_argument_away (harg w).1 (harg w).2
  have hb (w : InfinitePlace K) :
      ‖logDeriv mixedGammaAtom ((InfinitePlace.mult w : ℂ)*s/2)‖ ≤
        B*Real.log (|s.im|+2) := by
    apply (hbound _ (harg w).1 (harg w).2).trans
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.log_le_log (by positivity)
    have him : (((InfinitePlace.mult w : ℂ)*s/2).im) =
        (InfinitePlace.mult w : ℝ)*s.im/2 := by simp
    rw [him,abs_div,abs_mul,abs_of_nonneg (hm₀ w)]
    norm_num
    nlinarith [abs_nonneg s.im,hm₂ w]
  apply (mixedGammaFactor_logDeriv_norm_le_of_bounds_away K ha hb).trans
  have hlog : 0 < Real.log (|s.im|+2) := Real.log_pos (by linarith [abs_nonneg s.im])
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  have hp := mul_nonneg hn (mul_nonneg hB.le hlog.le)
  nlinarith

end
end ArtinMatthews.VaryingKummerAnalytic
