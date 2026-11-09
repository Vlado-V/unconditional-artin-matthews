module

public import ArtinMatthews.SourceArchProjectiveUpperAction


set_option backward.privateInPublic true
@[expose] public section

/-! Equivariance of every actual matrix Gram coordinate under the projective action. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

def sourceArchUpperOrigin : SourceArchUpperHalfSpace := (0, ⟨1, zero_lt_one⟩)

lemma sourceArchUpperHalfSection_origin : sourceArchUpperHalfSection sourceArchUpperOrigin = 1 := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchUpperHalfSection, sourceArchUpperOrigin, upperSection] <;> rfl

lemma sourceArchGLUpperAction_origin (a : GL (Fin 2) ℂ) :
    sourceArchGLUpperAction a sourceArchUpperOrigin = sourceArchGramCoordinates a := by
  rw [sourceArchGLUpperAction, sourceArchUpperHalfSection_origin, mul_one]

lemma sourceArchGramCoordinates_mul (a b : GL (Fin 2) ℂ) :
    sourceArchGramCoordinates (a * b) =
      sourceArchGLUpperAction a (sourceArchGramCoordinates b) := by
  rw [← sourceArchGLUpperAction_origin, sourceArchGLUpperAction_mul,
    sourceArchGLUpperAction_origin]

end
end ArtinMatthews.SourceArchJacquet
