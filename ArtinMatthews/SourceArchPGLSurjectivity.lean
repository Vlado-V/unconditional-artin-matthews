module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.Analysis.Complex.Polynomial.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! Actual complex square roots give the surjection from SL2(C) to PGL2(C). -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix
open scoped MatrixGroups
noncomputable section

lemma sourceArchComplexUnitSquareRoot (u : ℂˣ) : ∃ v : ℂˣ, v ^ 2 = u := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : ℂ) (by norm_num : 0 < (2 : ℕ))
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hz
    exact u.ne_zero hz.symm
  refine ⟨Units.mk0 z hz0, Units.ext ?_⟩
  exact hz

theorem sourceArchSpecialLinear_toPGL_surjective :
    Function.Surjective (SpecialLinearGroup.toPGL : SL(2, ℂ) → PGL(2, ℂ)) := by
  have hp : Function.Surjective (ProjectiveSpecialLinearGroup.toPGL : PSL(2, ℂ) → PGL(2, ℂ)) :=
    ProjectiveSpecialLinearGroup.toPGL_surj_of_roots (by
      intro u
      simpa only [Fintype.card_fin] using sourceArchComplexUnitSquareRoot u)
  intro g
  obtain ⟨q, hq⟩ := hp g
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨m, hq⟩

end
end ArtinMatthews.SourceArchJacquet
