module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ValuedFieldTheory.LocalField.Padic.UnitDecomposition
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
import GaloisCohomology.ProfiniteIntegers.TopologicalGeneration


set_option backward.privateInPublic true
@[expose] public section

set_option autoImplicit false

/-!
# Basic topological product equivalences for profinite units

This module contains the reusable, inexpensive product equivalences used by
the compiled stages of the profinite-unit decomposition.
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.Padic

namespace ProfiniteUnitDecomposition.Internal

/-- The prime certificate shared by every compiled stage of the profinite
unit decomposition. -/
instance primeFact (p : Nat.Primes) : Fact p.1.Prime :=
  ⟨p.2⟩

end ProfiniteUnitDecomposition.Internal

/-- Coordinatewise product of topological multiplicative equivalences. -/
noncomputable def continuousMulEquivPiCongr
    {ι : Type*} {A B : ι → Type*}
    [(i : ι) → TopologicalSpace (A i)]
    [(i : ι) → TopologicalSpace (B i)]
    [(i : ι) → Mul (A i)] [(i : ι) → Mul (B i)]
    (e : (i : ι) → A i ≃ₜ* B i) :
    ((i : ι) → A i) ≃ₜ* ((i : ι) → B i) :=
  { MulEquiv.piCongrRight fun i => (e i).toMulEquiv with
    continuous_toFun :=
      continuous_pi fun i =>
        (e i).continuous_toFun.comp (continuous_apply i)
    continuous_invFun :=
      continuous_pi fun i =>
        (e i).continuous_invFun.comp (continuous_apply i) }

/-- A product of pairs is topologically equivalent to the pair of products. -/
noncomputable def continuousMulEquivPiProd
    {ι : Type*} (A B : ι → Type*)
    [(i : ι) → TopologicalSpace (A i)]
    [(i : ι) → TopologicalSpace (B i)]
    [(i : ι) → Mul (A i)] [(i : ι) → Mul (B i)] :
    ((i : ι) → A i × B i) ≃ₜ*
      ((i : ι) → A i) × ((i : ι) → B i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_pi fun i =>
      continuous_fst.comp (continuous_apply i)).prodMk
        (continuous_pi fun i =>
          continuous_snd.comp (continuous_apply i))
  continuous_invFun :=
    continuous_pi fun i =>
      ((continuous_apply i).comp continuous_fst).prodMk
        ((continuous_apply i).comp continuous_snd)

/-- Multiplicative tagging commutes with topological products. -/
noncomputable def continuousPiMultiplicative
    {ι : Type*} (A : ι → Type*)
    [(i : ι) → TopologicalSpace (A i)]
    [(i : ι) → Add (A i)] :
    Multiplicative ((i : ι) → A i) ≃ₜ*
      ((i : ι) → Multiplicative (A i)) :=
  { MulEquiv.piMultiplicative A with
    continuous_toFun :=
      continuous_pi fun i => continuous_apply i
    continuous_invFun :=
      continuous_pi fun i => continuous_apply i }

/-- The product of all finite factors in the local unit decompositions. -/
noncomputable abbrev CyclotomicFinitePart :=
  (p : Nat.Primes) → padicUnitFiniteFactor p.1

end KummerTheory
