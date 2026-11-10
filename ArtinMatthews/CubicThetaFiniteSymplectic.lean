module

public import ArtinMatthews.CubicThetaFiniteLatticeArithmetic
public import ArtinMatthews.CubicThetaSymplecticEmbedding
public import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.PhaseAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


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
