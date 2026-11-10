module

public import ArtinMatthews.SpectralJGaussianFubini
public import ArtinMatthews.SpectralExpWeightedL1
public import ArtinMatthews.SpectralJGaussianExponentialDecay
public import ArtinMatthews.SpectralJGaussianSquareVariable
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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


set_option backward.privateInPublic true
@[expose] public section

/-! The noncompact profile errors retain the actual positive-half-line transform. -/
namespace ArtinMatthews
open Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem spectralJGaussianTransform_exp_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℝ → ℂ) (_ : ContDiff ℝ 2 d) (ε : ℝ), 0 ≤ ε →
      (∀ s : ℝ, 0 ≤ s → ‖d s‖ ≤ ε * Real.exp (-s) ∧
        ‖deriv d s‖ ≤ ε * Real.exp (-s) ∧
        ‖deriv (deriv d) s‖ ≤ ε * Real.exp (-s)) →
      let f := fun x : ℝ => (x : ℂ) * d (x ^ 2)
      IntegrableOn f (Ioi (0 : ℝ)) ∧ Measurable (spectralJGaussianTransform f) ∧
        ∀ w : ℝ, 0 < w → ‖spectralJGaussianTransform f w‖ ≤ C * ε / w := by
  obtain ⟨C, hC, hbound⟩ := spectralJGaussianSquared_error_bound
  refine ⟨C / 2, by positivity, ?_⟩
  intro d hd ε hε henv
  let f := fun x : ℝ => (x : ℂ) * d (x ^ 2)
  have hdI : IntegrableOn d (Ioi (0 : ℝ)) :=
    (integrable_norm_iff hd.continuous.aestronglyMeasurable).mp
      (spectralExpEnvelope_weightedL1 hd henv).2.1.1
  have hfI : IntegrableOn f (Ioi (0 : ℝ)) := (spectralSquare_integrable d).mpr hdI
  have hf : Continuous f := Complex.ofRealCLM.continuous.mul
    (hd.continuous.comp (continuous_id.pow 2))
  refine ⟨hfI, (spectralJGaussianTransform_continuous f hf hfI).measurable, ?_⟩
  intro w hw
  change ‖spectralJGaussianTransform f w‖ ≤ _
  rw [spectralJGaussianTransform_square d w, norm_mul]
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hhalf]
  have he := hbound d hd.contDiffOn ε hε
    (fun s hs => (henv s hs.le).1) (fun s hs => (henv s hs.le).2.1)
    (fun s hs => (henv s hs.le).2.2) w hw
  exact (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)

end
end ArtinMatthews
