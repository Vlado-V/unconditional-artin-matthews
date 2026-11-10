module

public import ArtinMatthews.SpectralDecayingPoincare
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
public import Mathlib.RingTheory.Radical.NatInt
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

/-! The literal inverse conversion from the unit-width physical KL test
to the native height profile. The square-root width is retained. -/

noncomputable section
open Set
open scoped ContDiff
namespace ArtinMatthews

def spectralNativeHeightProfileValue (q w : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.sqrt (y/w)*g ((q/w)*y)

theorem spectralNativeHeightProfileValue_smooth {q w : ℝ} (hq : 0 < q) (hw : 0 < w)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ))) :
    ContDiffOn ℝ ∞ (spectralNativeHeightProfileValue q w g) (Ioi (0 : ℝ)) := by
  have hs : ContDiffOn ℝ ∞ (fun y : ℝ => Real.sqrt (y/w)) (Ioi (0 : ℝ)) :=
    (contDiffOn_id.div_const w).sqrt (fun y hy => (div_pos hy hw).ne')
  have ha : ContDiffOn ℝ ∞ (fun y : ℝ => (q/w)*y) (Ioi (0 : ℝ)) :=
    contDiffOn_const.mul contDiffOn_id
  exact hs.mul (hg.comp ha (fun y hy => mul_pos (div_pos hq hw) hy))

theorem spectralNativeHeightProfile_power_factor {q w y : ℝ}
    (hq : 0 < q) (hw : 0 < w) (hy : 0 < y) (C E : ℝ) :
    Real.sqrt (y/w)*(C*((q/w)*y)^E) =
      (C*(q/w)^E/Real.sqrt w)*y^(E+1/2) := by
  rw [Real.sqrt_div hy.le w,Real.mul_rpow (div_pos hq hw).le hy.le,
    Real.rpow_add hy,Real.sqrt_eq_rpow]
  ring

def spectralNativeHeightProfile {q w B C : ℝ} (hq : 0 < q) (hw : 0 < w)
    (hB : 1/2 < B) (hC : 0 ≤ C) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ ∞ g (Ioi (0 : ℝ)))
    (hsmall : ∀ x, 0 < x → ‖g x‖ ≤ C*x^B)
    (hlarge : ∀ x, 0 < x → ‖g x‖ ≤ C*x^(-B-1)) : SpectralDecayingHeightProfile where
  value := spectralNativeHeightProfileValue q w g
  smooth := spectralNativeHeightProfileValue_smooth hq hw g hg
  exponent := B+1/2
  exponent_gt_one := by linarith
  bound := max (C*(q/w)^B/Real.sqrt w) (C*(q/w)^(-B-1)/Real.sqrt w)
  bound_nonneg := (by positivity : 0 ≤ C*(q/w)^B/Real.sqrt w).trans (le_max_left _ _)
  small_bound y hy := by
    rw [spectralNativeHeightProfileValue,norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (y/w)*(C*((q/w)*y)^B) := by gcongr; exact hsmall _ (mul_pos (div_pos hq hw) hy)
      _ = (C*(q/w)^B/Real.sqrt w)*y^(B+1/2) := spectralNativeHeightProfile_power_factor hq hw hy C B
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hy.le _)
  large_bound y hy := by
    rw [spectralNativeHeightProfileValue,norm_mul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc
      _ ≤ Real.sqrt (y/w)*(C*((q/w)*y)^(-B-1)) := by gcongr; exact hlarge _ (mul_pos (div_pos hq hw) hy)
      _ = (C*(q/w)^(-B-1)/Real.sqrt w)*y^(-(B+1/2)) := by
        rw [spectralNativeHeightProfile_power_factor hq hw hy C (-B-1)]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hy.le _)

theorem spectralNativeHeightProfileValue_physical {q w : ℝ}
    (hq : 0 < q) (hw : 0 < w) (g : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    spectralKLHeightPhysicalTest q
      (fun y => spectralNativeHeightProfileValue q w g (w*y)) x = (g x : ℂ) := by
  have hy : 0 < x/q := div_pos hx hq
  have h₁ : (w*(x/q))/w = x/q := by field_simp
  have h₂ : (q/w)*(w*(x/q)) = x := by field_simp
  unfold spectralKLHeightPhysicalTest spectralKLHeightBaseTest spectralNativeHeightProfileValue
  dsimp only
  rw [h₁,h₂]
  push_cast
  have hs : (Real.sqrt (x/q) : ℂ)^2 = (x/q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hy.le
  apply (div_eq_iff (div_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')
    (Complex.ofReal_ne_zero.mpr hq.ne'))).mpr
  calc
    _ = (g x : ℂ)*(Real.sqrt (x/q) : ℂ)^2 := by ring
    _ = _ := by rw [hs]

end ArtinMatthews
