module

public import Mathlib.Analysis.Complex.Norm
public import ArtinMatthews.MarkedMemoryGoodBoundary
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

/-! Finite composition of operators on an invariant weighted-energy
domain. This algebraic helper is used with the literal ghost and edge
operators, whose estimates are proved separately. -/

noncomputable section
namespace ArtinMatthews
open scoped BigOperators

def markedOperatorWord {Ω : Type*}
    (ghost edge : ℕ → (Ω → ℂ) → Ω → ℂ) : ℕ → ℕ → (Ω → ℂ) → Ω → ℂ
  | 0, j, f => ghost j f
  | n+1, j, f => ghost j (edge j (markedOperatorWord ghost edge n (j+1) f))

theorem markedOperatorWord_mem {Ω : Type*} (S : (Ω → ℂ) → Prop)
    (ghost edge : ℕ → (Ω → ℂ) → Ω → ℂ)
    (hg : ∀ j f, S f → S (ghost j f)) (he : ∀ j f, S f → S (edge j f))
    (f : Ω → ℂ) (hf : S f) (n j : ℕ) : S (markedOperatorWord ghost edge n j f) := by
  induction n generalizing j with
  | zero => exact hg j f hf
  | succ n ih => exact hg j _ (he j _ (ih (j+1)))

theorem markedOperatorWord_energy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (S : (Ω → ℂ) → Prop)
    (ghost edge : ℕ → (Ω → ℂ) → Ω → ℂ)
    (hg : ∀ j f, S f → S (ghost j f)) (he : ∀ j f, S f → S (edge j f))
    (C ε : ℝ)
    (hgE : ∀ j f, S f → (∑ s, μ s*‖ghost j f s‖^2) ≤ C^2*∑ s, μ s*‖f s‖^2)
    (heE : ∀ j f, S f → (∑ s, μ s*‖edge j f s‖^2) ≤ ε^2*∑ s, μ s*‖f s‖^2)
    (f : Ω → ℂ) (hf : S f) (n j : ℕ) :
    (∑ s, μ s*‖markedOperatorWord ghost edge n j f s‖^2) ≤
      (C^(n+1)*ε^n)^2*∑ s, μ s*‖f s‖^2 := by
  induction n generalizing j with
  | zero => simpa only [markedOperatorWord, pow_zero, Nat.zero_add, pow_one, mul_one] using hgE j f hf
  | succ n ih =>
    have hw := markedOperatorWord_mem S ghost edge hg he f hf n (j+1)
    calc
      _ ≤ C^2*(∑ s, μ s*‖edge j (markedOperatorWord ghost edge n (j+1) f) s‖^2) :=
        hgE j _ (he j _ hw)
      _ ≤ C^2*(ε^2*∑ s, μ s*‖markedOperatorWord ghost edge n (j+1) f s‖^2) :=
        mul_le_mul_of_nonneg_left (heE j _ hw) (sq_nonneg C)
      _ ≤ C^2*(ε^2*((C^(n+1)*ε^n)^2*∑ s, μ s*‖f s‖^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih (j+1)) (sq_nonneg ε)) (sq_nonneg C)
      _ = _ := by rw [pow_succ, pow_succ]; ring

theorem markedWeightedBoundary_norm_le {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (hμ : ∀ s, 0 ≤ μ s) (b f : Ω → ℂ)
    (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hb : (∑ s, μ s*‖b s‖^2) ≤ D)
    (hf : (∑ s, μ s*‖f s‖^2) ≤ C^2*∑ s, μ s*‖b s‖^2) :
    ‖∑ s, (μ s : ℂ)*star (b s)*f s‖ ≤ D*C := by
  let E : ℝ := ∑ s, μ s*‖b s‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD hC)).mp
  calc
    _ ≤ E*(∑ s, μ s*‖f s‖^2) := markedWeightedBoundary_cauchy μ hμ b f
    _ ≤ E*(C^2*E) := mul_le_mul_of_nonneg_left hf hE
    _ = C^2*E^2 := by ring
    _ ≤ C^2*D^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hE hb 2) (sq_nonneg C)
    _ = _ := by ring

end ArtinMatthews
