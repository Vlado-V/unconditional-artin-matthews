module

public import ArtinMatthews.StandardAdelicWeilIndex
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The actual archimedean Weil factors are one at every complex place.
The proof uses analytic square invariance and the genuine complex square
root, so it compares no Haar or Gaussian choices by assumption. -/

namespace ArtinMatthews.QuadraticWeil

open NumberField
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]

local instance complexWeilCompletionCharZero (v : InfinitePlace F) : CharZero v.Completion :=
  ArchimedeanAdeles.Construction.completionCharZero F (.inl v)
local instance complexWeilCompletionMeasurable (v : InfinitePlace F) : MeasurableSpace v.Completion :=
  borel v.Completion
local instance complexWeilCompletionBorel (v : InfinitePlace F) : BorelSpace v.Completion := ⟨rfl⟩

theorem standardNormalizedWeil_complex (v : InfinitePlace F) (hv : v.IsComplex) (a : Fˣ) :
    standardNormalizedWeil F a (.inl v) = 1 := by
  let C := v.Completion
  let e : C ≃+* ℂ := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv
  let x : Cˣ := Units.map (ArchimedeanAdeles.Construction.rationalScalar F (.inl v)).toMonoidHom a
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (x : C)) (by decide : 0 < 2)
  let y : C := e.symm z
  have hy : y ^ 2 = (x : C) := by
    apply e.injective
    simpa only [map_pow, y, e.apply_symm_apply] using hz
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hy
    exact x.ne_zero hy.symm
  let b : Cˣ := Units.mk0 y hy0
  have hb : b ^ 2 = x := Units.ext hy
  let ψ := Characters.Construction.localAdditiveCharacter F (StandardAdelic.character F) (.inl v)
  have hsq := analyticNormalizedWeil_square_mul (completion_nondiscrete F (.inl v)) ψ
    (AdelicCharacterData.local_continuous F _ (StandardAdelic.character_data F) (.inl v))
    (AdelicCharacterData.local_unitary F _ (StandardAdelic.character_data F) (.inl v))
    ((StandardAdelic.character_data F).local_nontrivial (.inl v)) 1 b
  have hreduce : analyticNormalizedWeil ψ x = analyticNormalizedWeil ψ 1 := by
    simpa only [one_mul, hb] using hsq
  change analyticNormalizedWeil ψ x = 1
  rw [hreduce]
  simpa only [standardNormalizedWeil, adelicNormalizedWeil, analyticNormalizedWeil,
    Units.val_one, map_one, mul_one] using standardNormalizedWeil_one F (.inl v)

theorem standardNormalizedWeil_infinite [IsTotallyComplex F] (v : InfinitePlace F) (a : Fˣ) :
    standardNormalizedWeil F a (.inl v) = 1 :=
  standardNormalizedWeil_complex F v (IsTotallyComplex.isComplex v) a

end

end ArtinMatthews.QuadraticWeil
