module

public import ArtinMatthews.SourceArchCasimirLogIdentities
public import ArtinMatthews.SourceArchDiagonalCompact


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceArchJacquet
open Matrix Matrix.GeneralLinearGroup
open scoped MatrixGroups
noncomputable section

theorem sourceArchUpperSection_zero (s : ℂ) (g : GL (Fin 2) ℂ) (z : ℂ) :
    sourceArchUpperSection s g z 0 = sourceArchSphericalGL s g := by
  simp only [sourceArchUpperSection, Complex.ofReal_zero, zero_mul,
    sourceKPUpperMatrix_zero, mul_one]

theorem sourceArchDiagonalSection_zero (s : ℂ) (g : GL (Fin 2) ℂ) :
    sourceArchDiagonalSection s g 0 = sourceArchSphericalGL s g := by
  rw [sourceArchDiagonalSection, sourceArchPositiveDiagonal_zero, mul_one]

def sourceArchSphericalRightCasimir (s : ℂ) (g : GL (Fin 2) ℂ) : ℂ :=
  -(deriv (deriv (sourceArchUpperSection s g 1)) 0 +
    deriv (deriv (sourceArchUpperSection s g Complex.I)) 0 +
    deriv (deriv (sourceArchDiagonalSection s g)) 0 -
    2 * deriv (sourceArchDiagonalSection s g) 0)

theorem sourceArchSphericalRightCasimir_eq (s : ℂ) (g : GL (Fin 2) ℂ) :
    sourceArchSphericalRightCasimir s g = (1-4*s^2)*sourceArchSphericalGL s g := by
  have hs : (sourceArchUpperLogOne g 1 0 : ℂ)^2 +
      (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 +
      (sourceArchDiagonalLogOne g 0 : ℂ)^2 = 1 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).1
  have hl : (sourceArchUpperLogTwo g 1 0 : ℂ) +
      (sourceArchUpperLogTwo g Complex.I 0 : ℂ) +
      (sourceArchDiagonalLogTwo g 0 : ℂ) - 2*(sourceArchDiagonalLogOne g 0 : ℂ) = -2 := by
    exact_mod_cast (sourceArchCasimir_log_identities g).2
  have he : sourceArchSphericalRightCasimir s g =
      -((2*s+1)^2*((sourceArchUpperLogOne g 1 0 : ℂ)^2 +
          (sourceArchUpperLogOne g Complex.I 0 : ℂ)^2 + (sourceArchDiagonalLogOne g 0 : ℂ)^2) +
        (2*s+1)*((sourceArchUpperLogTwo g 1 0 : ℂ) +
          (sourceArchUpperLogTwo g Complex.I 0 : ℂ) + (sourceArchDiagonalLogTwo g 0 : ℂ) -
          2*(sourceArchDiagonalLogOne g 0 : ℂ))) * sourceArchSphericalGL s g := by
    rw [sourceArchSphericalRightCasimir, sourceArchUpperSection_deriv_two,
      sourceArchUpperSection_deriv_two, sourceArchDiagonalSection_deriv_two,
      sourceArchDiagonalSection_deriv]
    simp only [sourceArchUpperSectionTwo, sourceArchDiagonalSectionTwo,
      sourceArchDiagonalSectionOne, sourceArchUpperSection_zero, sourceArchDiagonalSection_zero]
    ring
  rw [he,hs,hl]
  ring

end
end ArtinMatthews.SourceArchJacquet
