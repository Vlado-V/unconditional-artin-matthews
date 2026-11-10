/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: deprecated theorem aliases renamed to their
   declared replacements. Original: Charlie Dorsey, Weil Bounds Toolkit,
   commit 0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import rml.carlitz.relevant_irred
public import rml.carlitz.class_ghost
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Irreducible-class ghost sums

Expresses the extension sum using irreducible polynomial classes, in the Carlitz
(1969) recurrence framework.
-/

namespace RML.ExpSum.Carlitz

open Polynomial

noncomputable def irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) : ℂ := by
  classical
  letI : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  letI := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  letI : Fintype (RelevantIrred p n) :=
    Fintype.ofEquiv
      (ConjRootClass (Fp p) (Ext p n))
      (classRelevantEquiv p n)
  exact ∑ P : RelevantIrred p n,
    (P.1.natDegree : ℂ) *
      RML.ExpSum.Dickson.etaPoly p t P.1 ^
        (n / P.1.natDegree)

lemma minpoly_zero_class_eq_X
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    (0 : ConjRootClass (Fp p) (Ext p n)).minpoly =
      (X : Polynomial (Fp p)) := by
  change minpoly (Fp p) (0 : Ext p n) = X
  simp

theorem classGhost_eq_irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    classGhost p n t = irredGhost p n t := by
  classical
  let : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  let := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  let e := classRelevantEquiv p n
  let : Fintype (RelevantIrred p n) :=
    Fintype.ofEquiv
      (ConjRootClass (Fp p) (Ext p n)) e
  unfold classGhost irredGhost
  refine Fintype.sum_equiv e
    (fun c : ConjRootClass (Fp p) (Ext p n) =>
      if c = 0 then (0 : ℂ)
      else (c.minpoly.natDegree : ℂ) *
        RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree))
    (fun P : RelevantIrred p n =>
      (P.1.natDegree : ℂ) *
        RML.ExpSum.Dickson.etaPoly p t P.1 ^
          (n / P.1.natDegree)) ?_
  intro c
  change
    (if c = 0 then (0 : ℂ)
      else (c.minpoly.natDegree : ℂ) *
        RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree)) =
      (c.minpoly.natDegree : ℂ) *
        RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
          (n / c.minpoly.natDegree)
  by_cases hc : c = 0
  · subst c
    rw [ite_eq_left rfl, minpoly_zero_class_eq_X p n]
    simp [RML.ExpSum.Dickson.etaPoly]
    rw [zero_pow (NeZero.ne n)]
  · rw [ite_eq_right hc]

theorem Kext_eq_irredGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    Kext p n t = irredGhost p n t := by
  rw [Kext_eq_classGhost, classGhost_eq_irredGhost]

#print axioms classGhost_eq_irredGhost
#print axioms Kext_eq_irredGhost

end RML.ExpSum.Carlitz
