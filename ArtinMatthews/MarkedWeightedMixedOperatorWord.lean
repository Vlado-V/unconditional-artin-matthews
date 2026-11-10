module

public import ArtinMatthews.MarkedWeightedOperatorWord
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

/-! A stage-dependent edge budget in the actual invariant-energy domain.
This keeps crude costs on modified edges separate from signed contraction
on untouched edges. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedOperatorEdgeBudget (E : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,_ => 1
  | n+1,j => E j*markedOperatorEdgeBudget E n (j+1)

theorem markedOperatorWord_variable_energy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (S : (Ω → ℂ) → Prop)
    (ghost edge : ℕ → (Ω → ℂ) → Ω → ℂ)
    (hg : ∀ j f, S f → S (ghost j f)) (he : ∀ j f, S f → S (edge j f))
    (C : ℝ) (E : ℕ → ℝ)
    (hgE : ∀ j f, S f → (∑ s, μ s*‖ghost j f s‖^2) ≤ C^2*∑ s, μ s*‖f s‖^2)
    (heE : ∀ j f, S f → (∑ s, μ s*‖edge j f s‖^2) ≤ (E j)^2*∑ s, μ s*‖f s‖^2)
    (f : Ω → ℂ) (hf : S f) (n j : ℕ) :
    (∑ s, μ s*‖markedOperatorWord ghost edge n j f s‖^2) ≤
      (C^(n+1)*markedOperatorEdgeBudget E n j)^2*∑ s, μ s*‖f s‖^2 := by
  induction n generalizing j with
  | zero => simpa only [markedOperatorWord,markedOperatorEdgeBudget,Nat.zero_add,pow_one,mul_one] using hgE j f hf
  | succ n ih =>
    have hw := markedOperatorWord_mem S ghost edge hg he f hf n (j+1)
    calc
      _ ≤ C^2*(∑ s, μ s*‖edge j (markedOperatorWord ghost edge n (j+1) f) s‖^2) := hgE j _ (he j _ hw)
      _ ≤ C^2*((E j)^2*∑ s, μ s*‖markedOperatorWord ghost edge n (j+1) f s‖^2) :=
        mul_le_mul_of_nonneg_left (heE j _ hw) (sq_nonneg C)
      _ ≤ C^2*((E j)^2*((C^(n+1)*markedOperatorEdgeBudget E n (j+1))^2*
          ∑ s, μ s*‖f s‖^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih (j+1)) (sq_nonneg _)) (sq_nonneg C)
      _ = _ := by simp only [markedOperatorEdgeBudget,pow_succ]; ring

end ArtinMatthews
