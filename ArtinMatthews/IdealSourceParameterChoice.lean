module

public import ArtinMatthews.IdealSourceParameterDefinitions
public import ArtinMatthews.IdealSourceCoefficientCost
public import ArtinMatthews.IdealSourceScalarChoice
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The probe number is fixed before the comparison precision and
kernel cost. The copied dimension and growing carriers come afterward. -/
namespace ArtinMatthews
noncomputable section

theorem idealSource_parameter_choice (c₀ C₀ v₀ d C E : ℝ) (ell : ℕ)
    (hc₀ : 0 < c₀) (hC₀ : 0 ≤ C₀) (hd : 0 ≤ d) (hC : 0 ≤ C) (hE : 0 ≤ E) :
    ∃ m : ℕ, 1 ≤ m ∧ 0 < (2/(m+1 : ℕ) : ℝ) ∧ (2/(m+1 : ℕ) : ℝ) < 1 ∧
      (0 ≤ idealSourceErrorExponent E C₀ m ∧
       0 ≤ idealSourceRationalExponent E C₀ v₀ d m ∧
       1 ≤ idealSourceWidthExponent E C₀ v₀ d C m ∧
       0 ≤ idealSourceThresholdExponent E C₀ v₀ d C m ∧
       0 ≤ idealSourceCostExponent E C₀ v₀ d C m) ∧
      ∀ J : ℕ, idealSourceDimensionThreshold m ell ≤ J →
        m ≤ J ∧ (m+ell)*(m+ell-1) ≤ J+ell ∧
        ∀ (L : ℝ) (b s₁ s₂ P : ℕ), 2 ≤ L → (b : ℝ) ≤ C₀*Real.log L → P ≤ m*b →
          c₀*Real.log L/3 ≤ s₁ → c₀*Real.log L/3 ≤ s₂ →
          (Real.sqrt ((2/(m+1 : ℕ) : ℝ)^s₁)+Real.sqrt ((2/(m+1 : ℕ) : ℝ)^s₂)+
            (2 : ℝ)^P*L^(-idealSourceErrorExponent E C₀ m) ≤ L^(-E)) ∧
          ((1+(2 : ℝ)^P)*
            (1+(((⌊L^(idealSourceRationalExponent E C₀ v₀ d m)⌋₊ : ℕ) : ℝ)^2/
              L^(-idealSourceThresholdExponent E C₀ v₀ d C m))^2) ≤
            L^(idealSourceCostExponent E C₀ v₀ d C m)) := by
  obtain ⟨m, hm, hθ, hθ1, hJ, hbudget⟩ := idealSource_scalar_choice c₀ C₀ E ell hc₀ hC₀ hE
  refine ⟨m, hm, hθ, hθ1, idealSourceParameters_nonnegative hE hC₀ hd hC m, ?_⟩
  intro J hlarge
  have hdim := hJ J hlarge
  refine ⟨hdim.1, hdim.2, ?_⟩
  intro L b s₁ s₂ P hL hb hP hs₁ hs₂
  exact ⟨hbudget L b s₁ s₂ P hL hb hP hs₁ hs₂,
    idealSource_scalar_cost hE hC₀ hd hC hL hb hP⟩

end
end ArtinMatthews
