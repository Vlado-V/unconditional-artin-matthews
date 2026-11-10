module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.FullModulus
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
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
# Local conductor subgroups in the idele class group

This file records the one-place higher-unit subgroups used to compare
ray-class moduli with local conductors.  The constructions are
idele- and ray-class data and do not depend on the existence of a
global class field.
-/

open scoped NumberField

noncomputable section

namespace RayClass

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-- The image in `C_K` of the `n`-th higher-unit group at `v`. -/
def localHigherUnitClassSubgroup
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (IdeleClassGroup K) :=
  (localHigherUnitGroup v n).map
    (IdeleGroup.finitePlaceIdeleClass v)

/-- A one-place higher-unit condition is contained in the corresponding
global ray congruence subgroup. -/
theorem localHigherUnitClassSubgroup_le_congruenceSubgroup
    (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitClassSubgroup v (m.finitePart v) ≤
      m.congruenceSubgroup := by
  rintro _ ⟨x, hx, rfl⟩
  change
    IdeleGroup.finitePlaceIdeleClass v x ∈
      m.congruenceSubgroup
  rw [Modulus.congruenceSubgroup]
  refine ⟨IdeleGroup.finitePlaceIdele v x, ?_, rfl⟩
  apply Subgroup.mem_sup_left
  rw [Modulus.mem_ideleCongruenceSubgroup_iff]
  refine
    ⟨m.infiniteCongruenceSubgroup.one_mem, ?_⟩
  rw [mem_finiteCongruenceSubgroup_iff]
  intro w
  change
    IdeleGroup.finiteComponent w
        (IdeleGroup.finitePlaceIdele v x) ∈
      localHigherUnitGroup w (m.finitePart w)
  by_cases hw : w = v
  · subst w
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
    change
      x ∈
        (localHigherUnitGroup v (m.finitePart v) :
          Set (v.adicCompletion K)ˣ)
    exact hx
  · rw [
      IdeleGroup.finitePlaceIdele_finiteComponent_of_ne
        v w x hw]
    exact (localHigherUnitGroup w (m.finitePart w)).one_mem

end RayClass
