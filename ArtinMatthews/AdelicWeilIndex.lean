module

public import ArtinMatthews.BareLocalFourier
public import ArtinMatthews.AnalyticWeilSquareClasses


set_option backward.privateInPublic true
@[expose] public section

/-! Actual normalized analytic Weil indices of rational scalars at every
completion. Square invariance and nonvanishing are derived analytically. -/

namespace ArtinMatthews.QuadraticWeil

open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical

noncomputable section

variable (F : Type) [Field F] [NumberField F]
  (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)
  (d : AdelicCharacterData F ψ)

def adelicNormalizedWeil (x : Fˣ) (v : ArchimedeanAdeles.Construction.Places F) : ℂ :=
  OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v)
      (2 * ArchimedeanAdeles.Construction.rationalScalar F v (x : F)) /
    OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v) 2

theorem adelicNormalizedWeil_eq_local (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v =
      analyticNormalizedWeil (Characters.Construction.localAdditiveCharacter F ψ v)
        (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom x) := rfl

include d in
theorem adelicNormalizedWeil_square_mul (x y : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ (x * y ^ 2) v = adelicNormalizedWeil F ψ x v := by
  simpa only [adelicNormalizedWeil_eq_local, map_mul, map_pow] using
    analyticNormalizedWeil_square_mul (completion_nondiscrete F v)
      (Characters.Construction.localAdditiveCharacter F ψ v)
      (AdelicCharacterData.local_continuous F ψ d v)
      (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom x)
      (Units.map (ArchimedeanAdeles.Construction.rationalScalar F v).toMonoidHom y)

include d in
theorem adelicNormalizedWeil_eighth (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v ^ 8 = 1 := by
  rw [adelicNormalizedWeil_eq_local]
  exact analyticNormalizedWeil_eighth (completion_nondiscrete F v)
    (Characters.Construction.localAdditiveCharacter F ψ v)
    (AdelicCharacterData.local_continuous F ψ d v)
    (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v) _

include d in
theorem adelicNormalizedWeil_ne_zero (x : Fˣ)
    (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ x v ≠ 0 := by
  intro h
  have hh := adelicNormalizedWeil_eighth F ψ d x v
  rw [h, zero_pow (by decide)] at hh
  exact zero_ne_one hh

include d in
theorem adelicNormalizedWeil_one (v : ArchimedeanAdeles.Construction.Places F) :
    adelicNormalizedWeil F ψ 1 v = 1 := by
  have h := ((OAI.RepresentationTheory.Weil.Local.Analytic.Construction.localField_analytic_normalization
    (completion_nondiscrete F v) (Characters.Construction.localAdditiveCharacter F ψ v)
    (AdelicCharacterData.local_continuous F ψ d v)
    (AdelicCharacterData.local_unitary F ψ d v) (d.local_nontrivial v) 1).2.2.1 2
    (by norm_num)).2.2
  have hn : OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic.Construction.gaussianIndex
      (ArchimedeanAdeles.Construction.Completion F v)
      (Characters.Construction.localAdditiveCharacter F ψ v) 2 ≠ 0 := by
    intro hh
    rw [hh, zero_pow (by decide)] at h
    exact zero_ne_one h
  simpa only [adelicNormalizedWeil, Units.val_one, map_one, mul_one] using div_self hn

end

end ArtinMatthews.QuadraticWeil
