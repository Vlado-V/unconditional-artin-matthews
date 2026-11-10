module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Tactic.Basify
public import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitFactors
public import GaloisCohomology.ProfiniteIntegers.CyclotomicTorsionQuotient
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
# Torsion quotients of a profinite-integer product decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- A topological decomposition `G ≃ ℤ̂ × T` with dense torsion in `T`
identifies the quotient of `G` by the closure of its torsion with `ℤ̂`. -/
noncomputable def torsionQuotientEquivOfZHatMulDecomposition
    (G T : Type*) [CommGroup G] [CommGroup T]
    [TopologicalSpace G] [TopologicalSpace T]
    [IsTopologicalGroup G] [IsTopologicalGroup T]
    [CompactSpace G]
    (E : G ≃ₜ* Multiplicative ZHat × T)
    (hT : Dense (CommGroup.torsion T : Set T)) :
    G ⧸ (CommGroup.torsion G).topologicalClosure ≃ₜ*
      Multiplicative ZHat := by
  let fstHom :
      Multiplicative ZHat × T →*
        Multiplicative ZHat :=
    MonoidHom.fst _ _
  let freePart : G →* Multiplicative ZHat :=
    fstHom.comp E.toMonoidHom
  have hpreTorsion :
      E ⁻¹'
          (CommGroup.torsion
              (Multiplicative ZHat × T) :
            Set (Multiplicative ZHat × T)) =
        (CommGroup.torsion G : Set G) := by
    ext x
    change IsOfFinOrder (E x) ↔ IsOfFinOrder x
    exact Function.Injective.isOfFinOrder_iff
      (f := E.toMonoidHom) E.injective
  have hpreClosure :
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
        closure (CommGroup.torsion G : Set G) := by
    calc
      E ⁻¹'
          closure
            (CommGroup.torsion
                (Multiplicative ZHat × T) :
              Set (Multiplicative ZHat × T)) =
          closure
            (E ⁻¹'
              (CommGroup.torsion
                  (Multiplicative ZHat × T) :
                Set (Multiplicative ZHat × T))) :=
        E.toHomeomorph.preimage_closure _
      _ = closure (CommGroup.torsion G : Set G) := by
        rw [hpreTorsion]
  have hkerFst :
      fstHom.ker =
        (CommGroup.torsion
          (Multiplicative ZHat × T)).topologicalClosure := by
    rw [ClassFormation.topologicalClosure_torsion_zHatMul_prod T hT]
    ext x
    rcases x with ⟨x, y⟩
    change x = 1 ↔
      x ∈ (⊥ : Subgroup (Multiplicative ZHat)) ∧
        y ∈ (⊤ : Subgroup T)
    simp
  have hker :
      freePart.ker =
        (CommGroup.torsion G).topologicalClosure := by
    ext x
    change fstHom (E x) = 1 ↔
      x ∈ closure (CommGroup.torsion G : Set G)
    rw [← MonoidHom.mem_ker, hkerFst]
    exact Set.ext_iff.mp hpreClosure x
  have hsurj : Function.Surjective freePart := by
    intro z
    refine ⟨E.symm (z, 1), ?_⟩
    change fstHom (E (E.symm (z, 1))) = z
    rw [E.apply_symm_apply]
    rfl
  let e :
      G ⧸ (CommGroup.torsion G).topologicalClosure ≃*
        Multiplicative ZHat :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        freePart hsurj)
  exact
    LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivOfCompactToT2
        e
        (by
          rw [←
            QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
          exact continuous_fst.comp E.continuous_toFun)

end KummerTheory
