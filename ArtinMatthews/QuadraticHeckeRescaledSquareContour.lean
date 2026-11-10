module

public import ArtinMatthews.QuadraticHeckeCoprimeContourRemainder
public import ArtinMatthews.QuadraticHeckeSquareMellin
public import ArtinMatthews.QuadraticHeckeCoprimeDualSquareContour
public import ArtinMatthews.QuadraticHeckeCoprimeSquareContour
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

namespace ArtinMatthews
open NumberField Set VaryingKummerAnalytic
open scoped NumberField Classical ContDiff
noncomputable section

theorem quadraticHecke_square_norm_scale {M a : ℝ} (hM : 0 < M) (ha : 0 < a)
    (b : ℝ) : a * b ^ 2 / M = (b / Real.sqrt (M / a)) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (div_pos hM ha).le]
  field_simp [hM.ne', ha.ne']

variable (F : Type) [Field F] [NumberField F]

theorem quadraticHeckeCoprimeRescaledSquareContour_shift
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ M a : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hM : 0 < M) (ha : 0 < a) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then w (a * (Ideal.absNorm J.val : ℝ)^2 / M) else 0) =
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (mellin w)) σ (Real.sqrt (M / a)) +
      (dedekindZeta_residue F : ℂ) * (Real.sqrt (M / a) : ℂ) *
        ((1/2 : ℂ) * mellin w (1/2)) * quadraticHeckeCoprimeDensity F m := by
  simp_rw [quadraticHecke_square_norm_scale hM ha]
  exact quadraticHeckeCoprimeSquareNormContour_shift F m hm w hc hp hs hσ₀ hσ₁
    (Real.sqrt_pos.mpr (div_pos hM ha))

theorem quadraticHeckeCoprimeRescaledDualSquareContour_shift
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (A : ℝ) (r : ℕ) (w : ℝ → ℂ)
    (hc : HasCompactSupport w) (hp : tsupport w ⊆ Ioi 0) (hs : ContDiff ℝ ∞ w)
    {σ M a : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) (hM : 0 < M) (ha : 0 < a) :
    (∑' J : {J : Ideal (𝓞 F) // J ≠ ⊥},
      if IsCoprime J.val m then
        quadraticHeckeDualProfile A r w (a * (Ideal.absNorm J.val : ℝ)^2 / M) else 0) =
      quadraticHeckeCoprimeContourRemainder F m
        (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r w)) σ (Real.sqrt (M / a)) +
      (dedekindZeta_residue F : ℂ) * (Real.sqrt (M / a) : ℂ) *
        ((1/2 : ℂ) * mellin w (1/2)) * quadraticHeckeCoprimeDensity F m := by
  simp_rw [quadraticHecke_square_norm_scale hM ha]
  exact quadraticHeckeCoprimeDualSquareNormContour_shift F m hm A r w hc hp hs hσ₀ hσ₁
    (Real.sqrt_pos.mpr (div_pos hM ha))

end
end ArtinMatthews
