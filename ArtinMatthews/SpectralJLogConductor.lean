module

public import ArtinMatthews.SpectralJForwardTransform
public import ArtinMatthews.SpectralJLogSeminorm
public import ArtinMatthews.SpectralJLogParameterBounds
public import ArtinMatthews.SpectralJLogTransformBounds
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

/-! Conductor-power bounds for fixed compact logarithmic amplitudes and
phases, obtained from their proved Sturm seminorms. -/
namespace ArtinMatthews
open Set
open scoped ContDiff
noncomputable section

theorem spectralJOscillatoryLogProfile_conductor_estimates
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u Z P : ℝ, 0 < a → a ≤ R → 1+|u| ≤ Z →
      1 ≤ P → P⁻¹ ≤ a →
      (∀ t : ℝ,
        ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) (t : ℂ)‖ ≤
          C*P^δ/(1+|t|/Z)^N) ∧
      (∀ κ : ℝ, 0 ≤ κ → κ ≤ 1/4 →
        ‖spectralJForwardTransform (spectralJOscillatoryLogProfile A B a u) ((κ : ℂ)*Complex.I)‖ ≤
          C*P^δ*a^(-2*κ)) := by
  obtain ⟨D,hD,hreal⟩ := spectralJOscillatoryLogProfile_real_decay A B hA hB hs R hR N
  obtain ⟨E,hE,hexceptional⟩ := spectralJOscillatoryLogProfile_exceptional A B hA hB hs R hR
  obtain ⟨L,hL,hlog⟩ := spectralJLogScale_absorb R δ hδ
  let C := max (D*L) (E*L)
  refine ⟨C, (mul_pos hD hL).trans_le (le_max_left _ _), ?_⟩
  intro a u Z P ha haR hZ hP hPa
  have hp := hlog P a hP ha haR hPa
  constructor
  · intro t
    have hZ₀ : 0 < Z := by linarith [abs_nonneg u]
    have hden : 0 ≤ (1+|t|/Z)^N := by positivity
    calc
      _ ≤ D*(1+|Real.log a|)/(1+|t|/Z)^N := hreal a u t Z ha haR hZ
      _ ≤ D*(L*P^δ)/(1+|t|/Z)^N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hD.le) hden
      _ = (D*L)*P^δ/(1+|t|/Z)^N := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)) hden
  · intro κ hκ hκ₁
    have hpow : 0 ≤ a^(-2*κ) := Real.rpow_nonneg ha.le _
    calc
      _ ≤ E*(1+|Real.log a|)*a^(-2*κ) := hexceptional a u κ ha haR hκ hκ₁
      _ ≤ E*(L*P^δ)*a^(-2*κ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hE.le) hpow
      _ = (E*L)*P^δ*a^(-2*κ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _)) hpow

end
end ArtinMatthews
