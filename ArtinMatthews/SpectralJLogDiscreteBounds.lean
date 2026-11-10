module

public import ArtinMatthews.SpectralJLogSeminorm
public import ArtinMatthews.SpectralJOddCoefficients
public import ArtinMatthews.SpectralKLPhysicalCompactData
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

/-! Uniform factorial bounds for the actual discrete Bessel coefficients
of compact logarithmic source families. -/
namespace ArtinMatthews
open Set MeasureTheory
open SourceSturm
open scoped ContDiff
noncomputable section

theorem spectralJOscillatoryLogProfile_discrete_factorial
    (A : ℝ → ℂ) (B : ℝ → ℝ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    {α β : ℝ} (hs : tsupport A ⊆ Icc α β) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ a u : ℝ, 0 < a → a ≤ R → ∀ m : ℕ,
      ‖spectralJDiscreteCoefficient (spectralJOscillatoryLogProfile A B a u) m‖ ≤
        C*(a*Real.exp β/2)^m/(m.factorial : ℝ) := by
  obtain ⟨D,hD,hL⟩ := spectralJOscillatoryLogProfile_sturmL1 A B hA hB hs R hR 0
  let E := Real.exp ((R*Real.exp β)^2/4)
  refine ⟨E*D, mul_pos (Real.exp_pos _) hD, ?_⟩
  intro a u ha haR m
  let f := spectralJOscillatoryLogProfile A B a u
  have hgs : tsupport (markedOscillatoryFamily A B u) ⊆ Icc α β :=
    (spectralJOscillatoryFamily_tsupport A B u).trans hs
  have hfs : tsupport f ⊆ Icc (a*Real.exp α) (a*Real.exp β) :=
    spectralJLogProfile_tsupport ha hgs
  have hfp : tsupport f ⊆ Ioi 0 := spectralJLogProfile_positive_tsupport ha hgs
  have hf : ContDiff ℝ ∞ f := spectralJOscillatoryLogProfile_smooth A B hA hB hs ha u
  have hfc : HasCompactSupport f := spectralJLogProfile_hasCompactSupport ha hgs
  have hi : IntegrableOn (fun x : ℝ => f x/(x : ℂ)) (Ioi (0 : ℝ)) :=
    (spectralKLPhysicalCompactDiv_integrable f hf.continuous hfc hfp).restrict
  have hI : (∫ x in Ioi (0 : ℝ), ‖f x/(x : ℂ)‖) = sturmL1 f := by
    unfold sturmL1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ‖f x/(x : ℂ)‖ = ‖f x‖/x
    change 0 < x at hx
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  have hLnonneg : 0 ≤ sturmL1 f := by
    rw [← hI]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hL1 : sturmL1 f ≤ D := by
    simpa only [Function.iterate_zero, id_eq, Nat.mul_zero, pow_zero, mul_one] using hL a u ha haR
  have hE : Real.exp ((a*Real.exp β)^2/4) ≤ E := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (mul_nonneg ha.le (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_right haR (Real.exp_pos _).le) 2
  calc
    _ ≤ ((a*Real.exp β/2)^m/(m.factorial : ℝ)*Real.exp ((a*Real.exp β)^2/4)) *
        ∫ x in Ioi (0 : ℝ), ‖f x/(x : ℂ)‖ :=
      spectralJDiscreteCoefficient_norm_le f m (a*Real.exp β) (by positivity)
        (fun x hx => (hfs hx).2) hi
    _ ≤ ((a*Real.exp β/2)^m/(m.factorial : ℝ)*E)*D := by
      rw [hI]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) hL1
        hLnonneg (by positivity)
    _ = _ := by ring

end
end ArtinMatthews
