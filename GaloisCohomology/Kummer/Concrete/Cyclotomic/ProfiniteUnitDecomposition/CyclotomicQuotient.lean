module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Decomposition
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.DenseTorsion
public import GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientEquiv
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
# The cyclotomic profinite-unit torsion quotient
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- Cyclotomic-character form of the torsion decomposition: quotienting `ℤ̂ˣ` by
the closure of its torsion subgroup leaves one copy of `ℤ̂`. -/
noncomputable def zHatUnitsTorsionQuotientEquiv :
    ZHatˣ ⧸ (CommGroup.torsion ZHatˣ).topologicalClosure ≃ₜ*
      Multiplicative ZHat :=
  torsionQuotientEquivOfZHatMulDecomposition
    ZHatˣ CyclotomicFinitePart
      zHatUnitsDecomposition
        dense_torsion_cyclotomicFinitePart

end KummerTheory
