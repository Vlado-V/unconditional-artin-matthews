/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: proof-local letI spelling changed to let.
   Original: Charlie Dorsey, Weil Bounds Toolkit, commit
   0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import Mathlib.FieldTheory.Minpoly.ConjRootClass
public import rml.carlitz.extension_defs
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
# Irreducibles in the generating identity

Organizes the irreducible polynomial factors that contribute to the Carlitz (1969)
generating-series construction.
-/

namespace RML.ExpSum.Carlitz

open Polynomial

def RelevantIrred
    (p n : ℕ) [Fact p.Prime] :=
  {P : Polynomial (Fp p) //
    P.Monic ∧ Irreducible P ∧ P.natDegree ∣ n}

noncomputable def classToRelevant
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (c : ConjRootClass (Fp p) (Ext p n)) :
    RelevantIrred p n := by
  refine ⟨c.minpoly, c.monic_minpoly, c.irreducible_minpoly, ?_⟩
  have hd :
      c.minpoly.natDegree ∣
        Module.finrank (Fp p) (Ext p n) := by
    induction c with
    | h x =>
        simpa [ConjRootClass.minpoly_mk] using
          (minpoly.degree_dvd (IsIntegral.of_finite (Fp p) x))
  rw [GaloisField.finrank p (NeZero.ne n)] at hd
  exact hd

lemma classToRelevant_injective
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Function.Injective (classToRelevant p n) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg Subtype.val h

lemma classToRelevant_surjective
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    Function.Surjective (classToRelevant p n) := by
  intro P
  rcases P with ⟨P, hmonic, hirr, hdeg⟩
  let : Fact (Irreducible P) := ⟨hirr⟩
  let KP := AdjoinRoot P
  have hfinK :
      Module.finrank (Fp p) KP = P.natDegree := by
    exact finrank_quotient_span_eq_natDegree
  have hfinL :
      Module.finrank (Fp p) (Ext p n) = n :=
    GaloisField.finrank p (NeZero.ne n)
  have hdvd :
      Module.finrank (Fp p) KP ∣
        Module.finrank (Fp p) (Ext p n) := by
    rw [hfinK, hfinL]
    exact hdeg
  obtain ⟨phi⟩ :=
    FiniteField.nonempty_algHom_of_finrank_dvd
      (F := Fp p) (K := KP) (L := Ext p n) hdvd
  let x : Ext p n := phi (AdjoinRoot.root P)
  have hx : Polynomial.aeval x P = 0 := by
    have htransport :=
      Polynomial.hom_eval₂
        P (AdjoinRoot.of P) phi.toRingHom (AdjoinRoot.root P)
    rw [AdjoinRoot.eval₂_root, map_zero] at htransport
    have hcomp :
        phi.toRingHom.comp (AdjoinRoot.of P) =
          algebraMap (Fp p) (Ext p n) := by
      ext a
      exact phi.commutes a
    rw [hcomp] at htransport
    exact htransport.symm
  let c := ConjRootClass.mk (Fp p) x
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change c.minpoly = P
  rw [ConjRootClass.minpoly_mk]
  exact (minpoly.eq_of_irreducible_of_monic hirr hx hmonic).symm

noncomputable def classRelevantEquiv
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    ConjRootClass (Fp p) (Ext p n) ≃ RelevantIrred p n :=
  Equiv.ofBijective (classToRelevant p n)
    ⟨classToRelevant_injective p n,
     classToRelevant_surjective p n⟩

#print axioms classToRelevant_surjective

end RML.ExpSum.Carlitz
