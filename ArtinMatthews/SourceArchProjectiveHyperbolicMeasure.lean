module

public import ArtinMatthews.SourceArchProjectiveUpperAction
public import Mathlib.MeasureTheory.Measure.WithDensity


set_option backward.privateInPublic true
@[expose] public section

/-! Hyperbolic volume in the actual complex Gram chart is invariant under the full projective group. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix OAI.CubicEisenstein MeasureTheory
open scoped MatrixGroups
noncomputable section

def sourceArchHyperbolicMeasure : Measure SourceArchUpperHalfSpace :=
  Measure.map sourceArchHyperbolicHomeomorph.symm hyperbolicVolume

lemma sourceArchHyperbolicMeasure_specialLinear (a : SL(2, ℂ)) :
    Measure.map (sourceArchGLUpperAction (a : GL (Fin 2) ℂ)) sourceArchHyperbolicMeasure =
      sourceArchHyperbolicMeasure := by
  rw [sourceArchHyperbolicMeasure, Measure.map_map
    (sourceArchGLUpperAction_continuous _).measurable sourceArchHyperbolicHomeomorph.symm.measurable]
  have he : sourceArchGLUpperAction (a : GL (Fin 2) ℂ) ∘ sourceArchHyperbolicHomeomorph.symm =
      sourceArchHyperbolicHomeomorph.symm ∘ (fun w : HyperbolicSpace => a • w) := by
    funext w
    simp only [Function.comp_apply, sourceArchGLUpperAction_specialLinear, Homeomorph.apply_symm_apply]
  rw [he, ← Measure.map_map sourceArchHyperbolicHomeomorph.symm.measurable
    (continuous_hyperbolic_action a).measurable, hyperbolicVolume_invariant]

lemma sourceArchHyperbolicMeasure_projective (a : PGL(2, ℂ)) :
    Measure.map (sourceArchProjectiveUpperAction a) sourceArchHyperbolicMeasure =
      sourceArchHyperbolicMeasure := by
  obtain ⟨m, rfl⟩ := sourceArchSpecialLinear_toPGL_surjective a
  exact sourceArchHyperbolicMeasure_specialLinear m

lemma sourceArchHyperbolicMeasure_preserving (a : PGL(2, ℂ)) :
    MeasurePreserving (sourceArchProjectiveUpperAction a)
      sourceArchHyperbolicMeasure sourceArchHyperbolicMeasure :=
  ⟨(sourceArchProjectiveUpperAction_continuous a).measurable,
    sourceArchHyperbolicMeasure_projective a⟩

end
end ArtinMatthews.SourceArchJacquet
