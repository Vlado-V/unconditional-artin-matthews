module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Small conductor exponents leave four genuine Fourier height moments. -/

noncomputable section
namespace ArtinMatthews

theorem spectralABL_source_power_absorb {P₀ Z V S A B ν δ : ℝ}
    (hP₀ : 1 ≤ P₀) (hZ : 1 ≤ Z) (hV : 0 ≤ V) (hS : 0 ≤ S) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hν : (5/2)*δ ≤ ν) (hδ₁ : (5/2)*δ ≤ 1) :
    let P := P₀*Z
    P^δ*(1+P^(3*δ/2))*Real.sqrt (Z*V)*Real.sqrt S*
      Real.sqrt (Z^2+A)*Real.sqrt (Z^2+B*Z) ≤
      2*P₀^ν*Real.sqrt V*Real.sqrt S*Real.sqrt (1+A)*Real.sqrt (1+B)*Z^4 := by
  intro P
  have hP : 1 ≤ P := one_le_mul_of_one_le_of_one_le hP₀ hZ
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hZ₀ : 0 ≤ Z := zero_le_one.trans hZ
  have hE : 1 ≤ P^(3*δ/2) := Real.one_le_rpow hP (by positivity)
  have hPow : P^δ*(1+P^(3*δ/2)) ≤ 2*P₀^ν*Z := by
    calc
      _ ≤ P^δ*(2*P^(3*δ/2)) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2*P^((5/2)*δ) := by
        rw [show (5/2 : ℝ)*δ = δ+3*δ/2 by ring,Real.rpow_add hPpos]
        ring
      _ = 2*(P₀^((5/2)*δ)*Z^((5/2)*δ)) := by
        dsimp only [P]
        rw [Real.mul_rpow (zero_le_one.trans hP₀) hZ₀]
      _ ≤ _ := by
        have hL := Real.rpow_le_rpow_of_exponent_le hP₀ hν
        have hR : Z^((5/2)*δ) ≤ Z := (Real.rpow_le_rpow_of_exponent_le hZ hδ₁).trans_eq (Real.rpow_one Z)
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hL hR (by positivity) (by positivity)) (by norm_num)
  have hZ₂ : 1 ≤ Z^2 := one_le_pow₀ hZ
  have hSqrtZ : Real.sqrt Z ≤ Z :=
    (Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg hZ₀ (sub_nonneg.mpr hZ)] : Z ≤ Z^2)).trans_eq
      (Real.sqrt_sq hZ₀)
  have hRoot : Real.sqrt (Z*V) ≤ Z*Real.sqrt V := by
    rw [Real.sqrt_mul hZ₀]
    exact mul_le_mul_of_nonneg_right hSqrtZ (Real.sqrt_nonneg _)
  have hRootA : Real.sqrt (Z^2+A) ≤ Z*Real.sqrt (1+A) := by
    have he : Z^2+A ≤ Z^2*(1+A) := by
      nlinarith only [mul_nonneg hA (sub_nonneg.mpr hZ₂)]
    refine (Real.sqrt_le_sqrt he).trans_eq ?_
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hZ₀]
  have hRootB : Real.sqrt (Z^2+B*Z) ≤ Z*Real.sqrt (1+B) := by
    have he : Z^2+B*Z ≤ Z^2*(1+B) := by
      nlinarith only [mul_nonneg hB (mul_nonneg hZ₀ (sub_nonneg.mpr hZ))]
    refine (Real.sqrt_le_sqrt he).trans_eq ?_
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hZ₀]
  calc
    _ ≤ (2*P₀^ν*Z)*(Z*Real.sqrt V)*Real.sqrt S*
        (Z*Real.sqrt (1+A))*(Z*Real.sqrt (1+B)) := by
      gcongr
    _ = _ := by ring

end ArtinMatthews
