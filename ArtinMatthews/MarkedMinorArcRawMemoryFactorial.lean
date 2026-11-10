module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact finite factorial integration for indexed particle deletion. This
is the one-particle deletion/creation measure identity behind the actual
store/promote adjoint, before symmetric-function transport is applied. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Separating any one actual indexed particle preserves the literal
product integration, independently of its index or repeated values. -/
theorem markedRawMemory_delete_index_integral {X : Type*} [Fintype X]
    (μ : X → ℂ) (n : ℕ) (i : Fin (n+1)) (f : X → (Fin n → X) → ℂ) :
    (∑ a : Fin (n+1) → X, (∏ k, μ (a k))*f (a i) (Fin.removeNth i a))=
      ∑ p : X, ∑ b : Fin n → X, (μ p*(∏ k, μ (b k)))*f p b := by
  classical
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ : Fin (n+1) => X) i)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  change (∏ k, μ (Fin.insertNth (α := fun _ : Fin (n+1) => X) i p b k))*
    f (Fin.insertNth (α := fun _ : Fin (n+1) => X) i p b i)
      (Fin.removeNth i (Fin.insertNth (α := fun _ : Fin (n+1) => X) i p b))=_
  have hp := Fin.prod_univ_succAbove (fun k =>
    μ ((Fin.insertNthEquiv (fun _ : Fin (n+1) => X) i) (p,b) k)) i
  simpa only [Fin.insertNthEquiv_apply,Fin.insertNth_apply_same,Fin.removeNth_insertNth,
    Fin.insertNth_apply_succAbove] using congrArg (fun v : ℂ => v*f p b) hp

/-- Summing actual indexed deletion choices exactly changes the Fock factor
1/(n+1)! into 1/n!. This is an equality of genuine finite product sums,
with no restriction that numeric prime or anchor values be distinct. -/
theorem markedRawMemory_factorial_single_delete {X : Type*} [Fintype X]
    (μ : X → ℂ) (n : ℕ) (f : X → (Fin n → X) → ℂ) :
    (∑ a : Fin (n+1) → X, ((∏ k, μ (a k))/(Nat.factorial (n+1) : ℂ))*
      ∑ i : Fin (n+1), f (a i) (Fin.removeNth i a))=
      ∑ p : X, ∑ b : Fin n → X,
        ((μ p*(∏ k, μ (b k)))/(Nat.factorial n : ℂ))*f p b := by
  classical
  have hfac : (Nat.factorial n : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hfac' : (Nat.factorial (n+1) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+1)
  calc
    _ = ∑ i : Fin (n+1), (∑ a : Fin (n+1) → X,
        (∏ k, μ (a k))*f (a i) (Fin.removeNth i a))/(Nat.factorial (n+1) : ℂ) := by
      simp only [div_eq_mul_inv,Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ _i : Fin (n+1), (∑ p : X, ∑ b : Fin n → X,
        (μ p*(∏ k, μ (b k)))*f p b)/(Nat.factorial (n+1) : ℂ) := by
      simp only [markedRawMemory_delete_index_integral]
    _ = (n+1 : ℂ)*((∑ p : X, ∑ b : Fin n → X,
        (μ p*(∏ k, μ (b k)))*f p b)/(Nat.factorial (n+1) : ℂ)) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
    _ = _ := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      field_simp

end ArtinMatthews
