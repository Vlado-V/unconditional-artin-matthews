module

public import ArtinMatthews.SourceArchPGLSurjectivity
public import ArtinMatthews.SourceArchHyperbolicCoordinates


set_option backward.privateInPublic true
@[expose] public section

/-! The full complex projective action in literal Gram upper coordinates. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchGLUpperAction (a : GL (Fin 2) ℂ) (p : SourceArchUpperHalfSpace) :
    SourceArchUpperHalfSpace :=
  sourceArchGramCoordinates (a * sourceArchUpperHalfSection p)

lemma sourceArchGLUpperAction_scalar (a : GL (Fin 2) ℂ) (u : ℂˣ)
    (p : SourceArchUpperHalfSpace) :
    sourceArchGLUpperAction (a * GeneralLinearGroup.scalar (Fin 2) u) p =
      sourceArchGLUpperAction a p := by
  unfold sourceArchGLUpperAction
  rw [mul_assoc, GeneralLinearGroup.scalar_commute, ← mul_assoc,
    sourceArchGramCoordinates_scalar]

lemma sourceArchGLUpperAction_specialLinear (a : SL(2, ℂ)) (p : SourceArchUpperHalfSpace) :
    sourceArchGLUpperAction (a : GL (Fin 2) ℂ) p =
      sourceArchHyperbolicHomeomorph.symm (a • sourceArchHyperbolicHomeomorph p) := by
  apply sourceArchHyperbolicHomeomorph.injective
  rw [Homeomorph.apply_symm_apply]
  exact sourceArchHyperbolicHomeomorph_specialLinear_action a p

lemma sourceArchGLUpperAction_one (p : SourceArchUpperHalfSpace) :
    sourceArchGLUpperAction 1 p = p := by
  rw [sourceArchGLUpperAction, one_mul, sourceArchGramCoordinates_section]

lemma sourceArchGLUpperAction_mul (a b : GL (Fin 2) ℂ) (p : SourceArchUpperHalfSpace) :
    sourceArchGLUpperAction (a * b) p =
      sourceArchGLUpperAction a (sourceArchGLUpperAction b p) := by
  obtain ⟨s, hs⟩ := sourceArchSpecialLinear_toPGL_surjective (ProjGenLinGroup.mk a)
  obtain ⟨t, ht⟩ := sourceArchSpecialLinear_toPGL_surjective (ProjGenLinGroup.mk b)
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hs
  obtain ⟨v, hv⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp ht
  rw [← hu, ← hv]
  have hp : ((s : GL (Fin 2) ℂ) * GeneralLinearGroup.scalar (Fin 2) u) *
      ((t : GL (Fin 2) ℂ) * GeneralLinearGroup.scalar (Fin 2) v) =
      ((s * t : SL(2, ℂ)) : GL (Fin 2) ℂ) * GeneralLinearGroup.scalar (Fin 2) (u * v) := by
    rw [map_mul SpecialLinearGroup.toGL s t,
      map_mul (GeneralLinearGroup.scalar (Fin 2)) u v]
    calc
      _ = (s : GL (Fin 2) ℂ) * (GeneralLinearGroup.scalar (Fin 2) u * t) *
          GeneralLinearGroup.scalar (Fin 2) v := by group
      _ = (s : GL (Fin 2) ℂ) * ((t : GL (Fin 2) ℂ) * GeneralLinearGroup.scalar (Fin 2) u) *
          GeneralLinearGroup.scalar (Fin 2) v := by rw [GeneralLinearGroup.scalar_commute]
      _ = _ := by group
  rw [hp]
  simp only [sourceArchGLUpperAction_scalar, sourceArchGLUpperAction_specialLinear,
    mul_smul, Homeomorph.apply_symm_apply]

lemma sourceArchGLUpperAction_continuous (a : GL (Fin 2) ℂ) :
    Continuous (sourceArchGLUpperAction a) :=
  sourceArchGramCoordinates_continuous.comp (continuous_const.mul sourceArchUpperHalfSection_continuous)

def sourceArchProjectiveUpperAction (a : PGL(2, ℂ)) (p : SourceArchUpperHalfSpace) :
    SourceArchUpperHalfSpace :=
  Quotient.liftOn a (fun g => sourceArchGLUpperAction g p) (by
    intro g h hgh
    have he : ProjGenLinGroup.mk g = ProjGenLinGroup.mk h := Quotient.sound hgh
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp he
    rw [← hu, sourceArchGLUpperAction_scalar])

lemma sourceArchProjectiveUpperAction_mk (a : GL (Fin 2) ℂ) (p : SourceArchUpperHalfSpace) :
    sourceArchProjectiveUpperAction (ProjGenLinGroup.mk a) p =
      sourceArchGramCoordinates (a * sourceArchUpperHalfSection p) := rfl

lemma sourceArchProjectiveUpperAction_one (p : SourceArchUpperHalfSpace) :
    sourceArchProjectiveUpperAction 1 p = p := sourceArchGLUpperAction_one p

lemma sourceArchProjectiveUpperAction_mul (a b : PGL(2, ℂ)) (p : SourceArchUpperHalfSpace) :
    sourceArchProjectiveUpperAction (a * b) p =
      sourceArchProjectiveUpperAction a (sourceArchProjectiveUpperAction b p) := by
  induction a using ProjGenLinGroup.induction_on with | mk a =>
  induction b using ProjGenLinGroup.induction_on with | mk b =>
  exact sourceArchGLUpperAction_mul a b p

instance sourceArchProjectiveUpperMulAction : MulAction (PGL(2, ℂ)) SourceArchUpperHalfSpace where
  smul := sourceArchProjectiveUpperAction
  one_smul := sourceArchProjectiveUpperAction_one
  mul_smul := sourceArchProjectiveUpperAction_mul

lemma sourceArchProjectiveUpperAction_continuous (a : PGL(2, ℂ)) :
    Continuous (sourceArchProjectiveUpperAction a) := by
  induction a using ProjGenLinGroup.induction_on with | mk a =>
  exact sourceArchGLUpperAction_continuous a

end
end ArtinMatthews.SourceArchJacquet
