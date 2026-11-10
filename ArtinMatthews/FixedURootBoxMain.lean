module

public import ArtinMatthews.FixedURootBoxes
public import ArtinMatthews.FixedURootSLOrder
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

/-! The actual rectangular root-box cardinality with the special-linear main
term of PD (det:root-residue-count). The explicit error precedes the final
power-saving substitutions on the coordinate scales and the modulus. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The proved Euler coefficient is exactly the reciprocal special-linear mass. -/
theorem fixedURootBox_main_term_eq {S : ℕ} (hS : Squarefree S) (A B α β C D : ℝ) :
    ((β-α)*(D-C)/(S : ℝ)^2) *
      ((B-A)/(S : ℝ) * ((riemannZeta 2).re)⁻¹ *
        (∏ p ∈ S.primeFactors, (1-1/(p : ℝ)^2)⁻¹)) =
      ((B-A)*(β-α)*(D-C)) /
        ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) := by
  rw [squarefree_SL_two_card_real hS]
  simp only [div_eq_mul_inv,mul_inv_rev,Finset.prod_inv_distrib]
  ring

/-- The cardinality of the actual rectangular root set, with its exact
`volume/(ζ(2)*|SL₂(Z/S)|)` main term and fully explicit uniform error. -/
theorem fixedURootBox_card_error : ∃ K : ℝ, 0 < K ∧
    ∀ (N S : ℕ) (u₀ c₀ v₀ d₀ : ℤ) (A B α β C D : ℝ)
      (lcU rcU lcC rcC lcV rcV : Bool),
      0 < N → Squarefree S → Int.ModEq (S : ℤ) (u₀*d₀-c₀*v₀) 1 →
      1 ≤ A → A ≤ B → B ≤ N → 0 ≤ α → α ≤ β → β ≤ 1 → C ≤ D →
      |((fixedURootBoxPoints S u₀ c₀ v₀ d₀ A B α β C D
          lcU rcU lcC rcC lcV rcV).card : ℝ) -
        ((B-A)*(β-α)*(D-C)) /
          ((riemannZeta 2).re *
            (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
        K * B^(99/100 : ℝ) * (S : ℝ)^2 * (2+(D-C)/A) *
          ((B-A)/(S : ℝ)+1) + ((β-α)*(D-C)/(S : ℝ)^2)*(2+Real.log N) := by
  obtain ⟨K,hK,hcount⟩ := fixedURootBoxCount_zeta_error
  refine ⟨K,hK,?_⟩
  intro N S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hN hS hdet hA hAB hBN hα hαβ hβ hCD
  have hh := hcount N S u₀ c₀ v₀ d₀ A B α β C D lcU rcU lcC rcC lcV rcV
    hN hS hdet hA hAB hBN hα hαβ hβ hCD
  rw [fixedURootBoxCount_eq_card,fixedURootBox_main_term_eq hS] at hh
  exact hh

end ArtinMatthews
