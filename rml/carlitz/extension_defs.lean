/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

module

/- Ported to Lean 4.35.0-rc3: deprecated theorem aliases renamed to their
   declared replacements. Original: Charlie Dorsey, Weil Bounds Toolkit,
   commit 0f3e4c3010bb0e7c4e514ddb5bd3a0a0e082bf68. Apache-2.0. -/

public import rml.weil.prime_foundation
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

@[expose] public section

/-!
# Extension-field Kloosterman sums

Defines additive characters, trace maps and sums over finite extensions. Compare
Carlitz (1969), equations (2.8)–(2.13); the exact Lean normalization is specified by
the definitions below.
-/

namespace RML.ExpSum.Carlitz

abbrev Fp (p : ℕ) := ZMod p
abbrev Ext (p n : ℕ) [Fact p.Prime] [NeZero n] := GaloisField p n

/-- Canonical additive character on the chosen degree-n extension:
the base standard additive character composed with algebra trace. -/
noncomputable def psiExt
    (p n : ℕ) [Fact p.Prime] [NeZero n] :
    AddChar (Ext p n) ℂ where
  toFun x := ZMod.stdAddChar (Algebra.trace (Fp p) (Ext p n) x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [map_add, AddChar.map_add_eq_mul]

/-- Carlitz extension-field Kloosterman sum in prime-modulus argument/sign convention. -/
noncomputable def Kext
    (p n : ℕ) [Fact p.Prime] [NeZero n] (t : Fp p) : ℂ := by
  classical
  letI := Fintype.ofFinite (Ext p n)
  exact ∑ x : Ext p n,
    if x = 0 then 0
    else psiExt p n
      (x + algebraMap (Fp p) (Ext p n) t * x⁻¹)

/-- Canonical degree-one change of variables from the base field. -/
noncomputable def degreeOneEquiv
    (p : ℕ) [Fact p.Prime] :
    Fp p ≃ₐ[Fp p] Ext p 1 :=
  (GaloisField.equivZmodP p).symm

lemma trace_degreeOneEquiv
    (p : ℕ) [Fact p.Prime] (x : Fp p) :
    Algebra.trace (Fp p) (Ext p 1) (degreeOneEquiv p x) = x := by
  rw [Algebra.trace_eq_of_algEquiv (degreeOneEquiv p) x]
  exact Algebra.trace_self_apply x

lemma psiExt_degreeOneEquiv
    (p : ℕ) [Fact p.Prime] (x : Fp p) :
    psiExt p 1 (degreeOneEquiv p x) = ZMod.stdAddChar x := by
  simp [psiExt, trace_degreeOneEquiv]

theorem Kext_one_eq_kloostermanSumPrime
    (p : ℕ) [Fact p.Prime] (t : Fp p) :
    Kext p 1 t = RML.ExpSum.Weil.kloostermanSumPrime p t 1 := by
  classical
  let := Fintype.ofFinite (Ext p 1)
  let e := degreeOneEquiv p
  unfold Kext RML.ExpSum.Weil.kloostermanSumPrime
  symm
  refine Fintype.sum_equiv e.toEquiv
    (fun x : Fp p =>
      if x = 0 then (0 : ℂ) else
        ZMod.stdAddChar (1 * x + t * x⁻¹))
    (fun y : Ext p 1 =>
      if y = 0 then (0 : ℂ) else
        psiExt p 1 (y + algebraMap (Fp p) (Ext p 1) t * y⁻¹)) ?_
  intro x
  by_cases hx : x = 0
  · subst hx
    simp [e, degreeOneEquiv]
  · have hex : e.toEquiv x ≠ 0 := by
      simpa using ((map_ne_zero e).2 hx)
    simp only [ite_eq_right hx, ite_eq_right hex]
    change ZMod.stdAddChar (1 * x + t * x⁻¹) =
      psiExt p 1
        (e x + algebraMap (Fp p) (Ext p 1) t * (e x)⁻¹)
    have het :
        e t = algebraMap (Fp p) (Ext p 1) t := by
      simpa using e.commutes t
    have harg :
        e (x + t * x⁻¹) =
          e x + algebraMap (Fp p) (Ext p 1) t * (e x)⁻¹ := by
      rw [map_add, map_mul, map_inv₀, het]
    rw [← harg, psiExt_degreeOneEquiv]
    simp

#print axioms Kext_one_eq_kloostermanSumPrime

end RML.ExpSum.Carlitz
