module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.Core
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleArtin
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalHilbertSymbol.FinitePlaceCharacterComparison
public import Mathlib.Data.Nat.Choose.Multinomial
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
# Finite support of finite-place Hilbert symbols

The finite-place Hilbert-symbol family is obtained by applying the Kummer
root character to the finite-place Artin factors of a principal idele.  Its
finite support therefore follows directly from the existing finite-support
theorem for those Artin factors; no second ramification-support construction
is needed here.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open KummerTheory
open Function

variable (K : Type) [Field K] [NumberField K]

/-- For fixed global units `a` and `b`, the finite-place Hilbert symbols are
nontrivial at only finitely many finite places. -/
theorem finitePlaceHilbertSymbol_hasFiniteMulSupport
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a b : Kˣ) :
    HasFiniteMulSupport
      (fun v : HeightOneSpectrum (𝓞 K) =>
        finitePlaceHilbertSymbol K n hnK hmu v a b) := by
  let L := chosenSimpleKummerExtension K n hnK b
  let _ : FiniteDimensional K L :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK b
  let _ : IsAbelianGalois K L :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu b
  let _ : NumberField L := NumberField.of_module_finite K L
  let chi : Gal(L/K) →* nthRootsSubgroup K (n : ℕ) :=
    (nthRootsSubgroupEquivOfPrimitiveRoots K L n hmu).symm.toMonoidHom.comp
      (chosenSimpleKummerRootCharacter K n hnK hmu b)
  have hArtin :
      HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
            (IdeleGroup.finiteComponent v
              (IdeleGroup.principalIdele K a))) :=
    finitePlaceArtinFactors_hasFiniteMulSupport
      (K := K) (L := L) (IdeleGroup.principalIdele K a)
  have hRoot :
      HasFiniteMulSupport
        (fun v : HeightOneSpectrum (𝓞 K) =>
          chi
            (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
              (IdeleGroup.finiteComponent v
                (IdeleGroup.principalIdele K a)))) :=
    hArtin.subset (mulSupport_comp_subset chi.map_one _)
  convert hRoot using 1
  funext v
  have hcomponent :
      (IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) =
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a := by
    apply Units.ext
    calc
      ((IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K a) :
          (v.adicCompletion K)ˣ) : v.adicCompletion K) =
          ((a : K) : v.adicCompletion K) :=
        IdeleGroup.finiteComponent_principalIdele a v
      _ = algebraMap K (v.adicCompletion K) (a : K) := by
        symm
        have hmap := congrFun
          (IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (R := 𝓞 K) (S := K) (K := K) (v := v)) (a : K)
        simpa using hmap
  rw [hcomponent]
  calc
    finitePlaceHilbertSymbol K n hnK hmu v a b =
        finitePlaceKummerRootCharacter K n hnK hmu v a b :=
      (finitePlaceKummerRootCharacter_localGlobal
        K n hnK hmu v a b).symm
    _ = chi
        (chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) := by
      change finitePlaceKummerRootCharacter K n hnK hmu v a b =
        finitePlaceKummerRootCharacterOfExtension K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v)
      exact
        (finitePlaceKummerRootCharacterOfExtension_eq K n hnK hmu v a b
          (chosenFinitePlaceExtension (L := L) v)).symm

end Reciprocity
end GlobalClassFieldTheory
