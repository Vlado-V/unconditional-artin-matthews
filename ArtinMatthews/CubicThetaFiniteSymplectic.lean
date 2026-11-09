module

public import ArtinMatthews.CubicThetaFiniteLatticeArithmetic
public import ArtinMatthews.CubicThetaSymplecticEmbedding


set_option backward.privateInPublic true
@[expose] public section

/-! Concrete finite-adelic momentum and position maps of the Eisenstein
symplectic embedding. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators MatrixGroups
open Matrix
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData
open OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction.TestTransport

/-- The actual integral modular matrices acting in the finite Weil model. -/
def eisensteinFiniteSymplectic : SL(2, ℤ) →* Sp (Fin 2) AQf :=
  (mapSp (algebraMap ℚ AQf)).comp
    (eisensteinSymplecticHom.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ)))

/-- Integral Gram matrix and its integral adjugate. -/
def eisensteinGramInt : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; -1, 2]
def eisensteinGramAdjInt : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 2]

theorem eisensteinFiniteSymplectic_momentum (γ : SL(2, ℤ)) (p q : Fin 2 → AQf) :
    finiteMomentum (eisensteinFiniteSymplectic γ) p q =
      finiteIntegerMatrixAction (Matrix.diagonal (fun _ : Fin 2 => γ 0 0)) p +
        finiteIntegerMatrixAction (γ 0 1 • eisensteinGramInt) q := by
  funext i
  fin_cases i <;>
    simp [finiteMomentum, eisensteinFiniteSymplectic, mapSp, eisensteinSymplecticHom,
      eisensteinSymplectic, eisensteinSymplecticMatrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, map_intCast, map_ofNat,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, eisensteinGram, eisensteinGramInv,
      finiteIntegerMatrixAction, eisensteinGramInt, Matrix.fromBlocks, Matrix.diagonal]

theorem eisensteinFiniteSymplectic_position (γ : SL(2, ℤ)) (p q : Fin 2 → AQf) :
    finitePosition (eisensteinFiniteSymplectic γ) p q =
      finiteScale ((γ 1 0 : ℚ) / 3) (finiteIntegerMatrixAction eisensteinGramAdjInt p) +
        finiteIntegerMatrixAction (Matrix.diagonal (fun _ : Fin 2 => γ 1 1)) q := by
  have htwo : algebraMap ℚ AQf (2 / 3) = 2 * algebraMap ℚ AQf (1 / 3) := by
    rw [show (2 / 3 : ℚ) = 2 * (1 / 3) by ring, map_mul, map_ofNat]
  have hc : algebraMap ℚ AQf ((γ 1 0 : ℚ) * (1 / 3)) =
      (γ 1 0 : AQf) * algebraMap ℚ AQf (1 / 3) := by
    rw [map_mul, map_intCast]
  funext i
  fin_cases i <;>
    simp [finitePosition, eisensteinFiniteSymplectic, mapSp, eisensteinSymplecticHom,
      eisensteinSymplectic, eisensteinSymplecticMatrix, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, map_intCast,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, eisensteinGram, eisensteinGramInv,
      finiteIntegerMatrixAction, eisensteinGramAdjInt, finiteScale, Matrix.fromBlocks, Matrix.diagonal]
    <;> rw [show (γ 1 0 : ℚ) / 3 = (γ 1 0 : ℚ) * (1 / 3) by ring] at *
    <;> simp only [htwo, hc] <;> ring

end ArtinMatthews
