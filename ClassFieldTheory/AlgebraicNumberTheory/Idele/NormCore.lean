module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
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
# The absolute norm of an idele

This file constructs the homomorphism `𝓝 : I_K → ℝ₊ˣ`. At a finite place a uniformizer contributes the norm
of its prime ideal; at infinity we divide by the normalized archimedean
norm.  This is the convention for which principal ideles have norm one.
-/

open scoped NumberField RestrictedProduct NNReal
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

/-- The norm of a unit in a normed field, as a positive real unit. -/
def nnnormUnitHom (F : Type*) [NormedField F] :
    Fˣ →* ℝ≥0ˣ :=
  Units.map (nnnormHom : F →*₀ ℝ≥0).toMonoidHom

@[simp]
theorem nnnormUnitHom_val (F : Type*) [NormedField F] (x : Fˣ) :
    ((nnnormUnitHom F x : ℝ≥0ˣ) : ℝ≥0) = ‖(x : F)‖₊ :=
  rfl

namespace InfiniteIdeleGroup

/-- The product of the normalized norms of all archimedean components. -/
def archimedeanNorm :
    InfiniteIdeleGroup K →* ℝ≥0ˣ where
  toFun a := ∏ w : InfinitePlace K,
    nnnormUnitHom w.Completion (component w a) ^ w.mult
  map_one' := by
    apply Finset.prod_eq_one
    intro w _
    rw [map_one, map_one, one_pow]
  map_mul' a b := by
    simp only [map_mul, Finset.prod_mul_distrib, mul_pow]

@[simp]
theorem archimedeanNorm_apply (a : InfiniteIdeleGroup K) :
    archimedeanNorm a =
      ∏ w : InfinitePlace K,
        nnnormUnitHom w.Completion (component w a) ^ w.mult :=
  rfl

end InfiniteIdeleGroup

namespace FiniteIdeleGroup

/-- The positive real unit given by the absolute norm of a finite prime. -/
def primeNorm (v : HeightOneSpectrum (𝓞 K)) : ℝ≥0ˣ :=
  Units.mk0 (v.asIdeal.absNorm : ℝ≥0)
    (HeightOneSpectrum.absNorm_ne_zero v)

/-- The homomorphism sending an integer exponent to the corresponding
power of the absolute norm of a finite prime. -/
def primeNormPowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun n => primeNorm v ^ n.toAdd)
    fun m n => by simp [zpow_add]

/-- The norm of a finitely supported divisor. -/
def divisorNorm :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →* ℝ≥0ˣ :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n =>
        primeNormPowerHom v (Multiplicative.ofAdd n))
    fun _ _ => Finsupp.prod_hom_add_index
      (fun v => primeNormPowerHom v)

/-- The finite part of the absolute idele norm. -/
def absoluteNorm :
    FiniteIdeleGroup K →* ℝ≥0ˣ :=
  (divisorNorm (K := K)).comp (valuationVector (K := K))

@[simp]
theorem absoluteNorm_apply (a : FiniteIdeleGroup K) :
    absoluteNorm a =
      (valuationVector a).toAdd.prod fun v n =>
        primeNorm v ^ n := by
  rfl

end FiniteIdeleGroup

namespace IdeleGroup

/-- The absolute norm on the idele group. -/
def absoluteNorm :
    IdeleGroup K →* ℝ≥0ˣ :=
  MonoidHom.mk'
    (fun a => FiniteIdeleGroup.absoluteNorm a.2 *
      (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹)
    fun a b => by
      simp only [map_mul, Prod.fst_mul, Prod.snd_mul, mul_inv_rev]
      ac_rfl

@[simp]
theorem absoluteNorm_apply (a : IdeleGroup K) :
    absoluteNorm a =
      FiniteIdeleGroup.absoluteNorm a.2 *
        (InfiniteIdeleGroup.archimedeanNorm a.1)⁻¹ :=
  rfl

/-- The norm-one ideles. -/
def normOneSubgroup : Subgroup (IdeleGroup K) :=
  (absoluteNorm (K := K)).ker

end IdeleGroup
