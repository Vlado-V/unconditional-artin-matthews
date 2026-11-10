module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.GlobalClassFieldTheory.IdealClassFieldTheory.IdealArtinQuotient
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


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Ideal Frobenius classes and the decomposition law

This file records the ideal-class-field ingredient of the decomposition
law.  A prime outside a defining modulus gives an element of the ideal
Artin quotient, and the first isomorphism theorem preserves its order.
The general unramified Galois identity `r * f = n` belongs to
`RamificationTheory.HilbertRamification.Dedekind.Basic`.
-/

open scoped NumberField Classical

noncomputable section

namespace GlobalClassFieldTheory
namespace IdealClassFieldTheory

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  ideleClassSubgroupNormal idealArtinKernelNormal

/-- The ideal-theoretic Frobenius class attached to a prime outside the
defining modulus.  Under global reciprocity this is the usual Frobenius
automorphism. -/
def idealFrobeniusClass
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    IdeleClassGroup K ⧸ N :=
  idealArtinMap m N hm
    (RayClass.primeToModulusIdeal m v hv)

/-- The order of the Artin image of `v` is the order of `v` modulo the
ideal group `H_m`. -/
theorem orderOf_idealFrobeniusClass
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support) :
    orderOf (idealFrobeniusClass m N hm v hv) =
      orderOf
        (QuotientGroup.mk' (idealArtinKernel m N hm)
          (RayClass.primeToModulusIdeal m v hv)) := by
  exact
    (idealClassQuotientEquivNormQuotient m N hm).orderOf_eq
      (QuotientGroup.mk' (idealArtinKernel m N hm)
        (RayClass.primeToModulusIdeal m v hv))

/-- A power of a prime ideal lies in the defining ideal group exactly
when the order of its class in `J_K^m / H_m` divides the exponent.

This is the precise group-theoretic form of the "smallest positive
`f` with `p^f ∈ H_m`" clause in the unramified decomposition law. -/
theorem primeIdeal_pow_mem_idealArtinKernel_iff_orderOf_dvd
    (m : RayClass.Modulus K)
    (N : Subgroup (IdeleClassGroup K))
    (hm : RayClass.Modulus.congruenceSubgroup m ≤ N)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ m.finitePart.support)
    (n : ℕ) :
    (RayClass.primeToModulusIdeal m v hv) ^ n ∈
        idealArtinKernel m N hm ↔
      orderOf
        (QuotientGroup.mk' (idealArtinKernel m N hm)
            (RayClass.primeToModulusIdeal m v hv)) ∣
        n := by
  constructor
  · intro hmem
    have hq :
        QuotientGroup.mk' (idealArtinKernel m N hm)
            ((RayClass.primeToModulusIdeal m v hv) ^ n) = 1 :=
      (QuotientGroup.eq_one_iff
        ((RayClass.primeToModulusIdeal m v hv) ^ n)).2 hmem
    apply orderOf_dvd_iff_pow_eq_one.2
    simpa only [map_pow] using hq
  · intro hdvd
    have hq :
        (QuotientGroup.mk' (idealArtinKernel m N hm)
            (RayClass.primeToModulusIdeal m v hv)) ^ n = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 hdvd
    apply
      (QuotientGroup.eq_one_iff
        ((RayClass.primeToModulusIdeal m v hv) ^ n)).1
    calc
      QuotientGroup.mk' (idealArtinKernel m N hm)
            ((RayClass.primeToModulusIdeal m v hv) ^ n) =
          (QuotientGroup.mk' (idealArtinKernel m N hm)
            (RayClass.primeToModulusIdeal m v hv)) ^ n :=
        map_pow _ _ n
      _ = 1 := hq

end IdealClassFieldTheory
end GlobalClassFieldTheory
