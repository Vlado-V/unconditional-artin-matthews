module

public import ArtinMatthews.MarkedMajorCharacterSource


set_option backward.privateInPublic true
@[expose] public section

/-! Literal identification of each six-character term with the two actual
endpoint coefficients and the original determinant cutoff. -/
namespace ArtinMatthews
open Finset
noncomputable section

theorem markedMajorIntegerDeterminant_real (z z' : ℕ×(ℕ×ℕ)) :
    (markedMajorIntegerDeterminant z z':ℝ) =
      markedMajorLabelTripleValue z-markedMajorLabelTripleValue z' := by
  simp only [markedMajorIntegerDeterminant,markedMajorLabelTripleValue,
    Int.cast_sub,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]

theorem markedMajor_character_term_eq {J J' : Type*} [Fintype J] [Fintype J']
    (S T : Finset (ℕ×(ℕ×ℕ))) (bands : J → Finset ℕ) (bands' : J' → Finset ℕ)
    (cutoff : ℝ → ℂ) (Y W modulation modulation' : ℝ) (β β' : ℕ → ℂ)
    (ψ : ℝ → ℂ) (q : ℕ) [NeZero q] (χ : AddChar (MarkedUnitTuple q) ℂ) (θ : ℝ) :
    markedMajorArcCharacterTerm S T
      (markedMajorBareTripleCoefficient bands cutoff Y W modulation β)
      (markedMajorBareConjugateTripleCoefficient bands' cutoff Y W modulation' β') ψ q χ θ Y =
    ∑ z ∈ S,∑ z' ∈ T,
      (markedMajorLabelTripleCoefficient bands cutoff (markedCoordinateDirichlet q χ 1) θ Y
        (markedCoordinateDirichlet q χ 2) W modulation (fun n => β n*markedCoordinateDirichlet q χ 3 n) z*
       markedMajorLabelConjugateTripleCoefficient bands' cutoff (markedCoordinateDirichlet q χ 0) (-θ) Y
        (markedCoordinateDirichlet q χ 4) W modulation' (fun n => β' n*markedCoordinateDirichlet q χ 5 n) z')*
      (ψ ((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y)*
       OAI.Problem337.RealPhase.phase (θ*((markedMajorLabelTripleValue z-markedMajorLabelTripleValue z')/Y))) := by
  unfold markedMajorArcCharacterTerm
  simp_rw [markedMajor_bare_left_twist,markedMajor_bare_right_twist,
    markedMajorIntegerDeterminant_real,mul_div_assoc]

end
end ArtinMatthews
