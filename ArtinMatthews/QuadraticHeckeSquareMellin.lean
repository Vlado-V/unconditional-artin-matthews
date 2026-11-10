module

public import ArtinMatthews.QuadraticHeckeDualProfile
public import ArtinMatthews.QuadraticHeckeDualInversion
public import ArtinMatthews.VaryingKummerAnalyticMixedFunctionalNormalization
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
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex MeasureTheory Set VaryingKummerAnalytic
open scoped ContDiff
noncomputable section

/-- Mellin symbol for composition with the positive square map. -/
def quadraticHeckeSquareMellin (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * H (s / 2)

theorem quadraticHeckeSquareMellin_inversion (H : ℂ → ℂ) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (quadraticHeckeSquareMellin H) x =
      mellinInv (σ / 2) H (x ^ 2) := by
  let f (t : ℝ) : ℂ := ((x ^ 2 : ℝ) : ℂ) ^ (-((σ / 2 : ℝ) + (t : ℂ) * I)) *
    H ((σ / 2 : ℝ) + (t : ℂ) * I)
  have he (t : ℝ) :
      (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
          quadraticHeckeSquareMellin H ((σ : ℂ) + (t : ℂ) * I) =
        (1 / 2 : ℂ) * f ((1 / 2 : ℝ) * t) := by
    have hline : ((σ : ℂ) + (t : ℂ) * I) / 2 =
        (σ / 2 : ℝ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hxpow : ((x ^ 2 : ℝ) : ℂ) ^ (-(((σ : ℂ) + (t : ℂ) * I) / 2)) =
        (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
      rw [positiveReal_cpow_eq_exp (pow_pos hx 2), positiveReal_cpow_eq_exp hx,
        Real.log_pow]
      push_cast
      congr 1
      ring
    unfold quadraticHeckeSquareMellin f
    rw [← hline, hxpow]
    ring
  simp only [mellinInv, smul_eq_mul, Complex.real_smul]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, (x : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) *
      quadraticHeckeSquareMellin H ((σ : ℂ) + (t : ℂ) * I)) =
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, f t
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  norm_num [Complex.real_smul]
  ring

theorem quadraticHeckeSquareMellin_dual_inversion (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {x : ℝ} (hx : 0 < x) :
    mellinInv (5 / 4) (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) x =
      quadraticHeckeDualProfile A r w (x ^ 2) := by
  rw [quadraticHeckeSquareMellin_inversion _ _ hx, ← quadraticHeckeDualProfileAt_eq_mellinInv]
  exact (quadraticHeckeDualProfileAt_eq A r w hc hp hs (σ := 1 / 2) (τ := (5 / 4) / 2)
    (by norm_num) (by norm_num) (pow_pos hx 2)).symm

theorem quadraticHeckeSquareMellin_dual_verticalIntegrable (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w) :
    Integrable (fun t : ℝ => quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)
      ((5 / 4 : ℂ) + t * I)) := by
  let f (t : ℝ) := quadraticHeckeDualMellin A r w (((5 / 8 : ℝ) : ℂ) + (t : ℂ) * I)
  have hf : Integrable f := quadraticHeckeDualMellin_verticalIntegrable A r w hc hp hs (by norm_num)
  have hscaled := hf.comp_mul_left' (by norm_num : (1 / 2 : ℝ) ≠ 0)
  apply (hscaled.const_mul (1 / 2 : ℂ)).congr
  filter_upwards with t
  unfold f quadraticHeckeSquareMellin
  congr 2
  push_cast
  ring

theorem quadraticHeckeSquareMellin_dual_half_eq (A : ℝ) (r : ℕ) (w : ℝ → ℂ) :
    quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w) 1 =
      quadraticHeckeSquareMellin (mellin w) 1 := by
  unfold quadraticHeckeSquareMellin
  rw [quadraticHeckeDualMellin_half]

end
end ArtinMatthews
