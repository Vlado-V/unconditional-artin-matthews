module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Continuity
public import ArtinMatthews.MarkedMinorArcRawMemoryFactorial
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

/-! Actual indexed particle symmetry and the factorial one-particle
creation/deletion pairing. This is finite Fock measure arithmetic, with
symmetric test functions explicitly retained in the statement. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The literal source symmetric-pending condition for one particle list. -/
def MarkedRawTupleSymmetric {X : Type*} (n : ℕ) (g : (Fin n → X) → ℂ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (a : Fin n → X), g (a ∘ σ)=g a

/-- Move a selected old index to the last slot, preserving the order of
all other indices. This is an actual permutation, not a value quotient. -/
def markedRawInsertToLast {n : ℕ} (i : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' (Fin.last n)).symm

/-- Indexed insertion is the literal last insertion followed by this index
permutation, even for repeated particle values. -/
theorem markedRawInsertToLast_comp {X : Type*} {n : ℕ} (i : Fin (n+1))
    (p : X) (b : Fin n → X) :
    Fin.insertNth (α := fun _ : Fin (n+1) => X) i p b=
      (Fin.snoc b p) ∘ markedRawInsertToLast i := by
  apply Fin.insertNth_eq_iff.mpr
  constructor
  · simp only [Function.comp_apply,markedRawInsertToLast,Equiv.trans_apply,
      finSuccEquiv'_at,finSuccEquiv'_symm_none,Fin.snoc_last]
  · funext k
    simp only [Fin.removeNth,Function.comp_apply,markedRawInsertToLast,Equiv.trans_apply,
      finSuccEquiv'_succAbove,finSuccEquiv'_symm_some,Fin.succAbove_last,Fin.snoc_castSucc]

/-- A genuinely symmetric pending test is unchanged by canonical ordering
of a singled-out deleted particle. -/
theorem markedRawTupleSymmetric_insert {X : Type*} {n : ℕ}
    (g : (Fin (n+1) → X) → ℂ) (hg : MarkedRawTupleSymmetric (n+1) g)
    (i : Fin (n+1)) (p : X) (b : Fin n → X) :
    g (Fin.insertNth (α := fun _ : Fin (n+1) => X) i p b)=g (Fin.snoc b p) := by
  rw [markedRawInsertToLast_comp]
  exact hg _ _

/-- The actual source symmetric test has the same value after separating
any old index into a deletion coordinate and the surviving old list. -/
theorem markedRawTupleSymmetric_delete {X : Type*} {n : ℕ}
    (g : (Fin (n+1) → X) → ℂ) (hg : MarkedRawTupleSymmetric (n+1) g)
    (a : Fin (n+1) → X) (i : Fin (n+1)) :
    g a=g (Fin.snoc (Fin.removeNth i a) (a i)) := by
  calc
    _ = g (Fin.insertNth (α := fun _ : Fin (n+1) => X) i (a i) (Fin.removeNth i a)) :=
      congrArg g (Fin.insertNth_self_removeNth i a).symm
    _ = _ := markedRawTupleSymmetric_insert g hg i _ _

/-- Genuine one-particle Fock adjoint integration: summing indexed eligible
deletions cancels the input factorial and creates the same particle against
the literal product measure at the output. Symmetry is an explicit source
function condition, and no operator estimate is a premise. -/
theorem markedRawMemory_factorial_delete_pairing {X : Type*} [Fintype X]
    (μ : X → ℂ) (n : ℕ) (g : (Fin (n+1) → X) → ℂ)
    (hg : MarkedRawTupleSymmetric (n+1) g) (hit : X → ℂ) (f : (Fin n → X) → ℂ) :
    (∑ a : Fin (n+1) → X, ((∏ k, μ (a k))/(Nat.factorial (n+1) : ℂ))*g a*
      ∑ i : Fin (n+1), hit (a i)*f (Fin.removeNth i a))=
      ∑ p : X, ∑ b : Fin n → X,
        ((μ p*(∏ k, μ (b k)))/(Nat.factorial n : ℂ))*g (Fin.snoc b p)*hit p*f b := by
  classical
  calc
    _ = ∑ a : Fin (n+1) → X, ((∏ k, μ (a k))/(Nat.factorial (n+1) : ℂ))*
        ∑ i : Fin (n+1), g (Fin.snoc (Fin.removeNth i a) (a i))*hit (a i)*f (Fin.removeNth i a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [markedRawTupleSymmetric_delete g hg a i]
      ring
    _ = _ := by
      rw [markedRawMemory_factorial_single_delete μ n (fun p b => g (Fin.snoc b p)*hit p*f b)]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro b _
      ring

end ArtinMatthews
