module

public import ArtinMatthews.CubicSieveDivisorCoprimeMain
public import ArtinMatthews.CubicSieveDivisorUnitEstimate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The explicit logarithmic divisor main term in each unit class. -/

noncomputable section
namespace ArtinMatthews

open Finset
open scoped BigOperators

def cubicSieveDivisorUnitModel (d : ℕ) (x : ℝ) : ℝ :=
  x / (d : ℝ) *
    ((Real.log x + 2 * Real.eulerMascheroniConstant - 1) * cubicSieveCoprimeDensity d -
      2 * cubicSieveCoprimeLogMoment d)

theorem cubicSieve_divisorUnitMain_model_error {d X : ℕ}
    (hd : 0 < d) (hdX : d ≤ X.sqrt) :
    |cubicSieveDivisorUnitMain d X - cubicSieveDivisorUnitModel d X| ≤
      13 * (2 : ℝ) ^ d.primeFactors.card * (X.sqrt : ℝ) + 8 * (X.sqrt : ℝ) := by
  let m := X.sqrt
  let D := (2 : ℝ) ^ d.primeFactors.card
  let A := cubicSieveCoprimeDensity d
  let B := cubicSieveCoprimeLogMoment d
  let S := (Icc 1 m).filter (fun a => a.Coprime d)
  let H := ∑ a ∈ S, (a : ℝ)⁻¹
  let C : ℝ := S.card
  let H₀ := (Real.log (m : ℝ) + Real.eulerMascheroniConstant) * A - B
  let C₀ := (m : ℝ) * A
  let F₀ := 2 * ((X : ℝ) / d) * H₀ - ((m : ℝ) / d) * C₀
  have hm : 0 < m := hd.trans_le hdX
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm₀ : (0 : ℝ) < m := zero_lt_one.trans_le hm₁
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd₀ : (0 : ℝ) < d := zero_lt_one.trans_le hd₁
  have hsq : (m : ℝ) ^ 2 ≤ X := by
    exact_mod_cast Nat.sqrt_le' X
  have htop : (X : ℝ) ≤ (m : ℝ) ^ 2 + 2 * (m : ℝ) := by
    have h : (X : ℝ) ≤ (m : ℝ) * (m : ℝ) + m + m := by
      exact_mod_cast Nat.sqrt_le_add X
    nlinarith only [h]
  have hx : (0 : ℝ) < X := (pow_pos hm₀ 2).trans_le hsq
  have hscale : (X : ℝ) / m ≤ 3 * (m : ℝ) := by
    apply (div_le_iff₀ hm₀).mpr
    nlinarith only [htop, mul_le_mul_of_nonneg_right hm₁ hm₀.le]
  have hXd := div_le_self hx.le hd₁
  have hmd := div_le_self hm₀.le hd₁
  have hH : |H - H₀| ≤ D * (2 / (m : ℝ)) := cubicSieve_coprime_harmonic_error hd.ne' hdX
  have hC : |C - C₀| ≤ D := cubicSieve_coprime_card_error hd.ne' m
  have hFirst : |cubicSieveDivisorUnitMain d X - F₀| ≤ 13 * D * (m : ℝ) := by
    change |2 * ((X : ℝ) / d) * H - ((m : ℝ) / d) * C - F₀| ≤ _
    rw [show 2 * ((X : ℝ) / d) * H - ((m : ℝ) / d) * C - F₀ =
      2 * ((X : ℝ) / d) * (H - H₀) - ((m : ℝ) / d) * (C - C₀) by dsimp only [F₀]; ring]
    calc
      _ ≤ |2 * ((X : ℝ) / d) * (H - H₀)| + |((m : ℝ) / d) * (C - C₀)| := abs_sub _ _
      _ ≤ 2 * (X : ℝ) * (D * (2 / (m : ℝ))) + (m : ℝ) * D := by
        rw [abs_mul (2 * ((X : ℝ) / d)) (H - H₀), abs_mul ((m : ℝ) / d) (C - C₀),
          abs_of_nonneg (by positivity : 0 ≤ 2 * ((X : ℝ) / d)),
          abs_of_nonneg (div_nonneg hm₀.le hd₀.le)]
        gcongr
      _ = 4 * D * ((X : ℝ) / m) + (m : ℝ) * D := by ring
      _ ≤ 4 * D * (3 * (m : ℝ)) + (m : ℝ) * D := by gcongr
      _ = _ := by ring
  have hlog : |2 * Real.log (m : ℝ) - Real.log (X : ℝ)| ≤ 2 / (m : ℝ) := by
    have hlow := Real.log_le_log (pow_pos hm₀ 2) hsq
    rw [Real.log_pow, Nat.cast_ofNat] at hlow
    rw [abs_of_nonpos (sub_nonpos.mpr hlow), neg_sub,
      ← show Real.log ((X : ℝ) / (m : ℝ) ^ 2) =
        Real.log (X : ℝ) - 2 * Real.log (m : ℝ) by
        rw [Real.log_div hx.ne' (pow_pos hm₀ 2).ne', Real.log_pow, Nat.cast_ofNat]]
    calc
      _ ≤ (X : ℝ) / (m : ℝ) ^ 2 - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx (pow_pos hm₀ 2))
      _ ≤ ((m : ℝ) ^ 2 + 2 * (m : ℝ)) / (m : ℝ) ^ 2 - 1 := by gcongr
      _ = _ := by
        field_simp
        ring
  obtain ⟨hA₀, hA₁⟩ : 0 ≤ A ∧ A ≤ 1 := cubicSieve_coprimeDensity_bounds hd.ne'
  have hSecond : |F₀ - cubicSieveDivisorUnitModel d X| ≤ 8 * (m : ℝ) := by
    rw [show F₀ - cubicSieveDivisorUnitModel d X =
      ((X : ℝ) / d) * (2 * Real.log (m : ℝ) - Real.log (X : ℝ)) * A +
        (((X : ℝ) - (m : ℝ) ^ 2) / d) * A by
      dsimp only [F₀, H₀, C₀, cubicSieveDivisorUnitModel, A, B]
      ring]
    calc
      _ ≤ |((X : ℝ) / d) * (2 * Real.log (m : ℝ) - Real.log (X : ℝ)) * A| +
          |(((X : ℝ) - (m : ℝ) ^ 2) / d) * A| := abs_add_le _ _
      _ ≤ (X : ℝ) * (2 / (m : ℝ)) + 2 * (m : ℝ) := by
        have hround : (((X : ℝ) - (m : ℝ) ^ 2) / d) ≤ 2 * (m : ℝ) :=
          (div_le_self (sub_nonneg.mpr hsq) hd₁).trans (by linarith only [htop])
        simp only [abs_mul, abs_of_nonneg (div_nonneg hx.le hd₀.le),
          abs_of_nonneg (div_nonneg (sub_nonneg.mpr hsq) hd₀.le), abs_of_nonneg hA₀]
        calc
          _ ≤ (X : ℝ) * (2 / (m : ℝ)) * 1 + 2 * (m : ℝ) * 1 := by gcongr
          _ = _ := by ring
      _ = 2 * ((X : ℝ) / m) + 2 * (m : ℝ) := by ring
      _ ≤ 2 * (3 * (m : ℝ)) + 2 * (m : ℝ) := by gcongr
      _ = _ := by ring
  exact (abs_sub_le _ F₀ _).trans (add_le_add hFirst hSecond)

theorem cubicSieve_divisorUnitCount_model_error {d X : ℕ}
    (hd : 0 < d) (hdX : d ≤ X.sqrt) (u : (ZMod d)ˣ) :
    |cubicSieveDivisorUnitCount d X u - cubicSieveDivisorUnitModel d X| ≤
      26 * (2 : ℝ) ^ d.primeFactors.card * (X.sqrt : ℝ) := by
  have hD : 1 ≤ (2 : ℝ) ^ d.primeFactors.card := one_le_pow₀ (by norm_num)
  have hDM := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg X.sqrt)
  exact (abs_sub_le _ (cubicSieveDivisorUnitMain d X) _).trans
    ((add_le_add (cubicSieve_divisorUnitCount_error d X hd u)
      (cubicSieve_divisorUnitMain_model_error hd hdX)).trans (by linarith only [hDM]))

end ArtinMatthews
