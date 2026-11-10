module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FreeCoordinate
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
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
# Finite-order local coordinates of profinite units
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- If the free `p`-adic coordinate of a profinite unit vanishes, its
actual `p`-adic unit coordinate has finite order. -/
theorem zHatUnit_padicCoordinate_isOfFinOrder_of_freeCoordinate_eq_zero
    (u : ZHatˣ) (p : Nat.Primes)
    (hfree :
      zHatToPadicInt p
          (Multiplicative.toAdd
            (zHatUnitsDecomposition u).1) = 0) :
    IsOfFinOrder
      (zHatUnitsContinuousMulEquivPrimeProduct u p) := by
  let a :=
    ((padicUnitDecomposition p.1).symm
      (zHatUnitsContinuousMulEquivPrimeProduct u p)).1
  have hsecond :
      ((padicUnitDecomposition p.1).symm
        (zHatUnitsContinuousMulEquivPrimeProduct u p)).2 = 1 := by
    apply Multiplicative.ext
    simpa using
      (zHatUnitsDecomposition_freeCoordinate u p).symm.trans hfree
  have hpair :
      IsOfFinOrder
        (a, (1 : Multiplicative ℤ_[p.1])) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨orderOf a, orderOf_pos a, ?_⟩
    ext
    · exact pow_orderOf_eq_one a
    · simp
  have hsource :
      (a, (1 : Multiplicative ℤ_[p.1])) =
        (padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p) := by
    apply Prod.ext
    · rfl
    · exact hsecond.symm
  have himage :
      IsOfFinOrder
        (padicUnitDecomposition p.1
          (a, (1 : Multiplicative ℤ_[p.1]))) :=
    (Function.Injective.isOfFinOrder_iff
      (f := (padicUnitDecomposition p.1).toMonoidHom)
      (padicUnitDecomposition p.1).injective).2 hpair
  rw [hsource,
    (padicUnitDecomposition p.1).apply_symm_apply] at himage
  exact himage

end KummerTheory
