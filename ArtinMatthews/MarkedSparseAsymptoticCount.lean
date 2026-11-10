module

public import ArtinMatthews.MarkedSparsePrimeMoments
public import ArtinMatthews.MarkedSparseAsymptotic
public import ArtinMatthews.MarkedSparsePrimeCount
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Covering.Besicovitch
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

/-! Subexponentially many separated large-value samples for the actual
shifted character polynomial, in the logarithmic prime-scale range. -/

namespace ArtinMatthews

open Filter ReusedMoments

/-- Uniformity includes the modulus, the character, the real frequency
shift, and every prime subset in the stated interval. -/
theorem markedPrimePolynomial_sparse_samples (c C₁ C₂ A : ℝ)
    (hc : 0 < c) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hA : 0 ≤ A) :
    ∀ᶠ L : ℝ in atTop, ∀ Y T : ℝ, 1 < Y →
      c * L^(1/(10:ℝ)) ≤ Real.log Y →
      Real.log Y ≤ C₁ * L^(1/(5:ℝ)) → 1 < T → Real.log T ≤ C₂ * L →
      ∀ (k : ℕ) (χ : DirichletCharacter ℂ k) (ξ : ℝ) (P : Finset ℕ),
      (∀ p ∈ P, p.Prime) → (∀ p ∈ P, (p : ℝ) ≤ 2*Y) →
      ∀ S : Finset ℝ, (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, ∀ s ∈ S, t ≠ s → 1 ≤ |t-s|) →
      (∀ t ∈ S, L^(-A) ≤ ‖markedPrimePolynomial P Y χ ξ t‖) →
      (S.card : ℝ) ≤ Real.exp (L^(91/(100:ℝ))) := by
  filter_upwards [marked_sparse_cost_log_scales c C₁ C₂ A hc hC₁ hC₂ hA,
    eventually_gt_atTop (0:ℝ)] with L hcost hL
  intro Y T hY hlo hhi hT hTU k χ ξ P hP hcap S hS hsep hlarge
  exact (markedPrimePolynomial_sample_cost P Y (by linarith) χ ξ
    (mrtAmplificationOrder Y T) hP hcap S (by linarith)
    (Real.rpow_pos_of_pos hL _) hS hsep hlarge).trans (hcost Y T hY hlo hhi hT hTU)

end ArtinMatthews
