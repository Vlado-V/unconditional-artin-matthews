module

public import Mathlib.FieldTheory.Minpoly.ConjRootClass
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

@[expose] public section

/-!
# Conjugate decomposition

Decomposes sums into Frobenius-conjugate classes in the extension-field argument of
Carlitz (1969).
-/

namespace RML.ExpSum.Carlitz

open Polynomial

noncomputable def conjSigmaEquiv
    (F L : Type*) [Field F] [Field L] [Algebra F L] :
    (Σ c : ConjRootClass F L, c.carrier) ≃ L where
  toFun z := z.2.1
  invFun x := ⟨ConjRootClass.mk F x, ⟨x, rfl⟩⟩
  left_inv z := by
    rcases z with ⟨c, ⟨x, hx⟩⟩
    have hc : ConjRootClass.mk F x = c :=
      ConjRootClass.mem_carrier.mp hx
    subst c
    rfl
  right_inv x := rfl

theorem sum_eq_sum_conjRootClass
    {F L M : Type*} [Field F] [Field L] [Algebra F L]
    [Fintype L] [Fintype (ConjRootClass F L)]
    [∀ c : ConjRootClass F L, Fintype c.carrier]
    [AddCommMonoid M] (f : L → M) :
    (∑ x : L, f x) =
      ∑ c : ConjRootClass F L, ∑ x : c.carrier, f x.1 := by
  classical
  symm
  rw [← Fintype.sum_sigma']
  exact Fintype.sum_equiv (conjSigmaEquiv F L)
    (fun z => f z.2.1) f (fun _ => rfl)

#print axioms sum_eq_sum_conjRootClass

end RML.ExpSum.Carlitz
