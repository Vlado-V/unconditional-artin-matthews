module

public import ArtinMatthews.SourceArchGramCoordinates
public import OAI.NumberTheory.DirichletL.Eisenstein.HyperbolicVolume
public import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents


set_option backward.privateInPublic true
@[expose] public section

/-! The actual Gram upper coordinates agree with the checked SL2 hyperbolic model. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchUpperCoordinatesHomeomorph : SourceArchUpperHalfSpace ≃ₜ UpperCoordinates where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def sourceArchHyperbolicHomeomorph : SourceArchUpperHalfSpace ≃ₜ HyperbolicSpace :=
  sourceArchUpperCoordinatesHomeomorph.trans upperCoordinatesHomeomorph

lemma sourceArchHyperbolicHomeomorph_apply (p : SourceArchUpperHalfSpace) :
    sourceArchHyperbolicHomeomorph p = upperPoint p.1 p.2.val p.2.property := rfl

lemma sourceArchHeight_specialLinear (m : SL(2, ℂ)) :
    sourceArchHeight (m : GL (Fin 2) ℂ) = liftedHeight m := by
  simp only [sourceArchHeight, SpecialLinearGroup.coeToGL_det, Units.val_one, norm_one,
    one_div, liftedHeight, rowEnergy, complexBottomRow, sourceArchBottomNorm]
  rfl

lemma sourceArchGramShift_specialLinear (m : SL(2, ℂ)) :
    sourceArchGramShift (m : GL (Fin 2) ℂ) = matrixHorizontal m := rfl

lemma sourceArchHyperbolicHomeomorph_gram_specialLinear (m : SL(2, ℂ)) :
    sourceArchHyperbolicHomeomorph (sourceArchGramCoordinates (m : GL (Fin 2) ℂ)) =
      (m : HyperbolicSpace) := by
  rw [sourceArchHyperbolicHomeomorph_apply, matrix_point_coordinates m]
  apply upperPoint_congr
  · exact sourceArchGramShift_specialLinear m
  · exact sourceArchHeight_specialLinear m

lemma sourceArchHyperbolicHomeomorph_specialLinear_action (m : SL(2, ℂ))
    (p : SourceArchUpperHalfSpace) :
    sourceArchHyperbolicHomeomorph
      (sourceArchGramCoordinates ((m : GL (Fin 2) ℂ) * sourceArchUpperHalfSection p)) =
      m • sourceArchHyperbolicHomeomorph p := by
  change sourceArchHyperbolicHomeomorph
    (sourceArchGramCoordinates ((m * upperSection p.1 p.2.val p.2.property : SL(2, ℂ)) : GL (Fin 2) ℂ)) = _
  rw [sourceArchHyperbolicHomeomorph_gram_specialLinear]
  rfl

end
end ArtinMatthews.SourceArchJacquet
