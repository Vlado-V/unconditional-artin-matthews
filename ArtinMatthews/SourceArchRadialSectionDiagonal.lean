module

public import ArtinMatthews.SourceArchRadialSection


set_option backward.privateInPublic true
@[expose] public section

/-! The literal upper-section radial curve is right diagonal multiplication. -/
namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup OAI.CubicEisenstein
open scoped MatrixGroups
noncomputable section

theorem sourceArchRadialFlow_section_diagonal (t : ℝ) (p : SourceArchUpperHalfSpace) :
    sourceArchRadialFlow t (sourceArchUpperHalfSection p) =
      sourceArchUpperHalfSection p * sourceArchPositiveDiagonal t := by
  have hz : sourceArchGramShift (sourceArchUpperHalfSection p) = p.1 :=
    congrArg Prod.fst (sourceArchGramCoordinates_section p)
  have hentry (i j : Fin 2) : sourceArchUpperHalfSection p i j =
      !![(Real.sqrt p.2.val : ℂ), p.1 / (Real.sqrt p.2.val : ℂ);
        0, (Real.sqrt p.2.val : ℂ)⁻¹] i j := rfl
  rw [sourceArchRadialFlow,hz]
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceArchRadialBorel_entry, sourceArchPositiveDiagonal, sourceKPDiagonalHom,
      hentry, Matrix.mul_apply, Fin.sum_univ_two,
      div_eq_mul_inv]
  all_goals ring

theorem sourceArchUpperHalfSection_diagonal_projective (t : ℝ) (p : SourceArchUpperHalfSpace) :
    ProjGenLinGroup.mk (sourceArchUpperHalfSection p * sourceArchPositiveDiagonal t) =
      ProjGenLinGroup.mk (sourceArchUpperHalfSection (sourceArchRadialPoint t p)) := by
  rw [← sourceArchRadialFlow_section_diagonal, sourceArchRadialFlow_section_projective]

end
end ArtinMatthews.SourceArchJacquet
