module

public import ArtinMatthews.SpectralJHolomorphicCoefficient
public import ArtinMatthews.SpectralJLogSeminorm
public import ArtinMatthews.SpectralJLogDiscreteBounds
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

/-! Source-uniform factorial bounds after the exact holomorphic
Petersson normalization, including the lowest weight. -/
namespace ArtinMatthews
open Set Complex
open scoped ContDiff
noncomputable section

theorem spectralJOscillatoryLogProfile_holomorphic_factorial
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ R → ∀ k : ℕ, 2 ≤ k →
      ‖spectralJHolomorphicCoefficient (spectralJOscillatoryLogProfile A B a u) k‖ ≤
        C*(a*Real.exp β/2)^(k-1)/((k-2).factorial : ℝ) := by
  obtain ⟨C,hC,hcoeff⟩ := spectralJOscillatoryLogProfile_discrete_factorial A B hA hB hs R hR
  refine ⟨C/Real.pi, div_pos hC Real.pi_pos, ?_⟩
  intro a u ha haR k hk
  let f := spectralJOscillatoryLogProfile A B a u
  have hnorm : ‖spectralJHolomorphicCoefficient f k‖ =
      ((k-1 : ℕ) : ℝ)/Real.pi * ‖spectralJDiscreteCoefficient f (k-1)‖ := by
    unfold spectralJHolomorphicCoefficient
    simp only [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_zpow, Complex.norm_I, one_zpow, mul_one]
  calc
    _ = ((k-1 : ℕ) : ℝ)/Real.pi * ‖spectralJDiscreteCoefficient f (k-1)‖ := hnorm
    _ ≤ ((k-1 : ℕ) : ℝ)/Real.pi *
        (C*(a*Real.exp β/2)^(k-1)/((k-1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (hcoeff a u ha haR (k-1)) (by positivity)
    _ = _ := by
      have hkm : k-1 = (k-2)+1 := by omega
      rw [hkm, Nat.factorial_succ]
      push_cast
      have hn : (((k-2 : ℕ) : ℝ)+1) ≠ 0 := by positivity
      field_simp [hn, Real.pi_ne_zero,
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k-2))] <;> ring

theorem spectralJOscillatoryLogProfile_weight_two
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ R →
      ‖spectralJHolomorphicCoefficient (spectralJOscillatoryLogProfile A B a u) 2‖ ≤
        C*a := by
  obtain ⟨C,hC,h⟩ := spectralJOscillatoryLogProfile_holomorphic_factorial A B hA hB hs R hR
  refine ⟨C*Real.exp β/2, by positivity, ?_⟩
  intro a u ha haR
  have htwo := h a u ha haR 2 (by decide)
  norm_num at htwo
  convert htwo using 1 <;> ring

end
end ArtinMatthews
