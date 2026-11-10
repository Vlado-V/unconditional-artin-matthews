/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: deprecated theorem aliases renamed to their
   declared replacements. Original: Charlie Dorsey, Weil Bounds Toolkit,
   commit 0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import Mathlib.FieldTheory.Minpoly.ConjRootClass
public import rml.carlitz.dickson_finite_algebra
public import rml.carlitz.extension_defs
public import Mathlib.Algebra.Lie.OfAssociative
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
public import Mathlib.RingTheory.PicardGroup
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
public import rml.carlitz.class_value
public import rml.carlitz.conj_decomp

@[expose] public section

/-!
# Conjugacy-class ghost sums

Conjugate polynomial classes and ghost sums used in the Carlitz recurrence. The
extension-sum method is from Carlitz (1969); the class decomposition is formalized
here.
-/

namespace RML.ExpSum.Carlitz

open Polynomial

lemma conjCarrier_card_eq_minpoly_natDegree
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    (c : ConjRootClass (Fp p) (Ext p n))
    [Fintype c.carrier] :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  let e : c.carrier ≃ c.minpoly.rootSet (Ext p n) := {
    toFun x := ⟨x.1, by
      rw [c.rootSet_minpoly_eq_carrier]
      exact x.2⟩
    invFun x := ⟨x.1, by
      rw [← c.rootSet_minpoly_eq_carrier]
      exact x.2⟩
    left_inv x := by apply Subtype.ext; rfl
    right_inv x := by apply Subtype.ext; rfl
  }
  calc
    Fintype.card c.carrier =
        Fintype.card (c.minpoly.rootSet (Ext p n)) :=
      Fintype.card_congr e
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree
        c.separable_minpoly c.splits_minpoly

lemma minpoly_eq_class_minpoly
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    {c : ConjRootClass (Fp p) (Ext p n)}
    (y : c.carrier) :
    minpoly (Fp p) (y : Ext p n) = c.minpoly := by
  have hy : ConjRootClass.mk (Fp p) (y : Ext p n) = c :=
    ConjRootClass.mem_carrier.mp y.2
  calc
    minpoly (Fp p) (y : Ext p n) =
        (ConjRootClass.mk (Fp p) (y : Ext p n)).minpoly := by
      symm
      exact ConjRootClass.minpoly_mk (K := Fp p) (y : Ext p n)
    _ = c.minpoly := congrArg ConjRootClass.minpoly hy

lemma relative_finrank_eq_total_div_classDegree
    (p n : ℕ) [Fact p.Prime] [NeZero n]
    {c : ConjRootClass (Fp p) (Ext p n)}
    (y : c.carrier) :
    Module.finrank
        (IntermediateField.adjoin (Fp p) ({(y : Ext p n)} : Set (Ext p n)))
        (Ext p n) =
      n / c.minpoly.natDegree := by
  let M :=
    IntermediateField.adjoin (Fp p) ({(y : Ext p n)} : Set (Ext p n))
  have hyint : IsIntegral (Fp p) (y : Ext p n) :=
    IsIntegral.of_finite (Fp p) (y : Ext p n)
  have hbase :
      Module.finrank (Fp p) M = c.minpoly.natDegree := by
    calc
      Module.finrank (Fp p) M =
          (minpoly (Fp p) (y : Ext p n)).natDegree :=
        IntermediateField.adjoin.finrank hyint
      _ = c.minpoly.natDegree := by
        rw [minpoly_eq_class_minpoly p n y]
  have htotal :
      Module.finrank (Fp p) (Ext p n) = n :=
    GaloisField.finrank p (NeZero.ne n)
  have hdegpos : 0 < c.minpoly.natDegree := by
    rw [← minpoly_eq_class_minpoly p n y]
    exact minpoly.natDegree_pos hyint
  have hbase0 : Module.finrank (Fp p) M ≠ 0 := by
    rw [hbase]
    exact hdegpos.ne'
  have hcancel :=
    Module.finrank_div_finrank_cancel_left
      (Fp p) M (Ext p n) hbase0
  calc
    Module.finrank M (Ext p n) =
        Module.finrank (Fp p) (Ext p n) /
          Module.finrank (Fp p) M := hcancel.symm
    _ = n / c.minpoly.natDegree := by
      rw [htotal, hbase]

#print axioms conjCarrier_card_eq_minpoly_natDegree
#print axioms relative_finrank_eq_total_div_classDegree


noncomputable def classGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) : ℂ := by
  classical
  letI : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  letI := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  exact ∑ c : ConjRootClass (Fp p) (Ext p n),
    if c = 0 then 0
    else (c.minpoly.natDegree : ℂ) *
      RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
        (n / c.minpoly.natDegree)

theorem Kext_eq_classGhost
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) :
    Kext p n t = classGhost p n t := by
  classical
  let := Fintype.ofFinite (Ext p n)
  let : Finite (ConjRootClass (Fp p) (Ext p n)) := by
    unfold ConjRootClass
    infer_instance
  let := Fintype.ofFinite (ConjRootClass (Fp p) (Ext p n))
  unfold Kext classGhost
  rw [sum_eq_sum_conjRootClass
    (F := Fp p) (L := Ext p n) (M := ℂ)]
  apply Fintype.sum_congr
  intro c
  by_cases hc : c = 0
  · subst c
    rw [ite_eq_left rfl]
    apply Fintype.sum_eq_zero
    intro y
    have hy0 : (y : Ext p n) = 0 :=
      (ConjRootClass.mk_eq_zero_iff (K := Fp p) (y : Ext p n)).mp y.2
    simp [hy0]
  · rw [ite_eq_right hc]
    calc
      (∑ y : c.carrier,
          if (y : Ext p n) = 0 then 0
          else psiExt p n
            ((y : Ext p n) +
              algebraMap (Fp p) (Ext p n) t * (y : Ext p n)⁻¹)) =
        ∑ _y : c.carrier,
          RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
            (n / c.minpoly.natDegree) := by
          apply Fintype.sum_congr
          intro y
          have hyne : (y : Ext p n) ≠ 0 := by
            intro hy0
            have hyc :
                ConjRootClass.mk (Fp p) (y : Ext p n) = c :=
              ConjRootClass.mem_carrier.mp y.2
            rw [hy0, ConjRootClass.mk_zero] at hyc
            exact hc hyc.symm
          rw [ite_eq_right hyne]
          rw [psiExt_carlitz_arg_eq_etaPoly_pow p n t hyne]
          rw [minpoly_eq_class_minpoly p n y]
          rw [relative_finrank_eq_total_div_classDegree p n y]
      _ =
        (c.minpoly.natDegree : ℂ) *
          RML.ExpSum.Dickson.etaPoly p t c.minpoly ^
            (n / c.minpoly.natDegree) := by
          rw [← conjCarrier_card_eq_minpoly_natDegree p n c]
          simp [nsmul_eq_mul]

#print axioms Kext_eq_classGhost

end RML.ExpSum.Carlitz
