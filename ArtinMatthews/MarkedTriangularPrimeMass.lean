module

public import ArtinMatthews.MarkedPrimeTuplePrefix
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
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

/-! Finite successive summation of nonnegative prime kernels depending
only on strict earlier prime values. Every conditional row is bounded
pointwise, so no independence of the imposed equality events is used. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedTriangularPrimeWeight {n : ℕ} (P : Fin n → Finset Nat.Primes)
    (k : (i : Fin n) → (Fin i.val → Nat.Primes) → ↥(P i) → ℝ)
    (t : (i : Fin n) → ↥(P i)) : ℝ :=
  ∏ i,k i (markedPrimeTuplePrefix t i) (t i)

theorem markedTriangularPrimeWeight_nonneg {n : ℕ} (P : Fin n → Finset Nat.Primes)
    (k : (i : Fin n) → (Fin i.val → Nat.Primes) → ↥(P i) → ℝ)
    (hk : ∀ i prior p,0 ≤ k i prior p) (t : (i : Fin n) → ↥(P i)) :
    0 ≤ markedTriangularPrimeWeight P k t :=
  Finset.prod_nonneg (fun i _ => hk i _ _)

theorem markedTriangularPrimeWeight_snoc {n : ℕ} (P : Fin (n+1) → Finset Nat.Primes)
    (k : (i : Fin (n+1)) → (Fin i.val → Nat.Primes) → ↥(P i) → ℝ)
    (t : (i : Fin n) → ↥(P i.castSucc)) (p : P (Fin.last n)) :
    markedTriangularPrimeWeight P k (Fin.snoc t p)=
      markedTriangularPrimeWeight (fun i => P i.castSucc) (fun i => k i.castSucc) t *
        k (Fin.last n) (fun i => (t i).1) p := by
  unfold markedTriangularPrimeWeight
  rw [Fin.prod_univ_castSucc]
  simp only [markedPrimeTuplePrefix_snoc_castSucc,markedPrimeTuplePrefix_snoc_last,
    Fin.snoc_castSucc,Fin.snoc_last]
  rfl

theorem markedTriangularPrimeMass_le : ∀ (n : ℕ) (P : Fin n → Finset Nat.Primes)
    (k : (i : Fin n) → (Fin i.val → Nat.Primes) → ↥(P i) → ℝ) (b : Fin n → ℝ),
    (∀ i prior p,0 ≤ k i prior p) → (∀ i,0 ≤ b i) →
    (∀ i prior,(∑ p : P i,k i prior p) ≤ b i) →
    (∑ t : (i : Fin n) → ↥(P i),markedTriangularPrimeWeight P k t) ≤ ∏ i,b i := by
  intro n
  induction n with
  | zero =>
    intro P k b hk hb hm
    simp [markedTriangularPrimeWeight]
  | succ n ih =>
    intro P k b hk hb hm
    let P₀ : Fin n → Finset Nat.Primes := fun i => P i.castSucc
    let k₀ : (i : Fin n) → (Fin i.val → Nat.Primes) → ↥(P₀ i) → ℝ := fun i => k i.castSucc
    let b₀ : Fin n → ℝ := fun i => b i.castSucc
    have hi := ih P₀ k₀ b₀ (fun i => hk i.castSucc) (fun i => hb i.castSucc) (fun i => hm i.castSucc)
    have he := Equiv.sum_comp (Fin.snocEquiv (fun i => ↥(P i))) (markedTriangularPrimeWeight P k)
    calc
      _ = ∑ p : P (Fin.last n),∑ t : (i : Fin n) → ↥(P₀ i),
          markedTriangularPrimeWeight P k (Fin.snoc t p) := by
        rw [← he,Fintype.sum_prod_type]
        rfl
      _ = ∑ t : (i : Fin n) → ↥(P₀ i),markedTriangularPrimeWeight P₀ k₀ t *
          (∑ p : P (Fin.last n),k (Fin.last n) (fun i => (t i).1) p) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro t _
        simp only [markedTriangularPrimeWeight_snoc]
        rw [Finset.mul_sum]
      _ ≤ ∑ t : (i : Fin n) → ↥(P₀ i),markedTriangularPrimeWeight P₀ k₀ t * b (Fin.last n) := by
        apply Finset.sum_le_sum
        intro t _
        exact mul_le_mul_of_nonneg_left (hm (Fin.last n) _)
          (markedTriangularPrimeWeight_nonneg P₀ k₀ (fun i => hk i.castSucc) t)
      _ = (∑ t : (i : Fin n) → ↥(P₀ i),markedTriangularPrimeWeight P₀ k₀ t) * b (Fin.last n) :=
        by rw [Finset.sum_mul]
      _ ≤ (∏ i : Fin n,b₀ i) * b (Fin.last n) := mul_le_mul_of_nonneg_right hi (hb (Fin.last n))
      _ = ∏ i,b i := (Fin.prod_univ_castSucc b).symm

end
end ArtinMatthews
