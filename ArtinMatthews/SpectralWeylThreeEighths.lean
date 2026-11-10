module

public import ArtinMatthews.SpectralWeylContourIntegrand
public import ArtinMatthews.SpectralWeylGammaPairBound
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open Complex
noncomputable section

theorem spectral_weyl_gamma_pair_three_eighths_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖spectralABLCoshCancellation ((t : ℂ)+((3/8 : ℝ) : ℂ)*I) /
        Complex.Gamma (1-2*I*((t : ℂ)+((3/8 : ℝ) : ℂ)*I))‖ ≤ C*(1+|t|) := by
  obtain ⟨C,hC,hbound⟩ := spectral_weyl_gamma_pair_shift_bound (3/8) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro t
  have h := hbound (-t)
  have hz : ((-t : ℝ) : ℂ)-((3/8 : ℝ) : ℂ)*I = -((t : ℂ)+((3/8 : ℝ) : ℂ)*I) := by
    push_cast
    ring
  have hd : 1+2*((3/8 : ℝ) : ℂ)+2*((-t : ℝ) : ℂ)*I =
      1-2*I*((t : ℂ)+((3/8 : ℝ) : ℂ)*I) := by
    push_cast
    ring_nf
    simp only [I_sq]
    ring
  simpa only [hz,hd,spectralABLCoshCancellation_even,abs_neg] using h

theorem spectralWeylContour_three_eighths_bound
    (cylinder : ℂ → ℝ → ℂ) (H base : ℂ → ℂ)
    (hFactor : ∀ z : ℂ, H z = base z * spectralABLCoshCancellation z)
    (hCylinder : ∀ X : ℝ, 0 < X → ∀ ν : ℂ, 0 ≤ ν.re →
      ‖cylinder ν X‖ ≤ (X/2)^ν.re*Real.exp (X^2/4)/‖Complex.Gamma (ν+1)‖)
    {B : ℝ} (hB : 0 < B)
    (hBase : ∀ t : ℝ, ‖base ((t : ℂ)+((3/8 : ℝ) : ℂ)*I)‖ ≤ B/(1+t^2)^2) :
    ∃ C : ℝ, 0 < C ∧ ∀ R X t : ℝ, 1 ≤ R → 0 < X →
      ‖spectralWeylContourIntegrand cylinder H R X ((t : ℂ)+((3/8 : ℝ) : ℂ)*I)‖ ≤
        C*((X/2)^(3/4 : ℝ)*Real.exp (X^2/4))/(1+t^2) := by
  obtain ⟨G,hG,hGamma⟩ := spectral_weyl_gamma_pair_three_eighths_bound
  refine ⟨2*B*Real.exp (25/32)*G, by positivity, ?_⟩
  intro R X t hR hX
  have hnorm : ‖(t : ℂ)+((3/8 : ℝ) : ℂ)*I‖ ≤ 1+|t| := by
    calc
      _ ≤ ‖(t : ℂ)‖+‖((3/8 : ℝ) : ℂ)*I‖ := norm_add_le _ _
      _ = |t|+3/8 := by norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by linarith
  have hGauss := spectralWeylGaussian_norm_bound hR t (3/8) (by norm_num)
  have hGamma := hGamma t
  have hpoint := spectralWeylContourIntegrand_norm_le cylinder H base R X t (3/8)
    hX (by norm_num) (hFactor _) (hCylinder X hX)
  norm_num only [show (2:ℝ)*(3/8)=3/4 by norm_num] at hpoint
  have hsquare : (1+|t|)^2 ≤ 2*(1+t^2) := by
    nlinarith [sq_abs t,sq_nonneg (|t|-1)]
  have hu : 0 < 1+t^2 := by positivity
  calc
    _ ≤ ((1+|t|)*(B/(1+t^2)^2)*Real.exp (25/32))*
        ((X/2)^(3/4 : ℝ)*Real.exp (X^2/4))*(G*(1+|t|)) := by
      apply hpoint.trans
      gcongr
      exact hBase t
    _ = (B*Real.exp (25/32)*G*((X/2)^(3/4 : ℝ)*Real.exp (X^2/4)))*
        ((1+|t|)^2/(1+t^2)^2) := by ring
    _ ≤ (B*Real.exp (25/32)*G*((X/2)^(3/4 : ℝ)*Real.exp (X^2/4)))*
        ((2*(1+t^2))/(1+t^2)^2) := by gcongr
    _ = _ := by field_simp

end
end ArtinMatthews
