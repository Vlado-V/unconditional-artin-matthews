module

public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.CubicThetaSiegelTransform
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic


set_option backward.privateInPublic true
@[expose] public section

/-!
Restriction of the existing rational Gaussian theta transformation to the
actual Eisenstein Siegel line. The finite Weil operator remains explicit;
scalar congruence covariance is a separate arithmetic conclusion.
-/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

/-- The genuine rational symplectic transformation, restricted to the
positive Eisenstein quadratic form and with zero Jacobi argument. -/
theorem eisensteinAdelicTheta_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (φ : finiteSchwartz (Fin 2)) (τ : ℍ) :
    theta (D.finiteAction (eisensteinSymplectic γ) φ) (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        theta φ (eisensteinSiegel τ) 0 := by
  have h := OAI.RepresentationTheory.Theta.PoissonAutomorphyGaussianParabolic.Construction.gaussian_theta_transformation
    D (eisensteinSymplectic γ) φ (eisensteinSiegel τ) 0
  simpa only [eisensteinSiegel_transform, map_zero, quadraticFactor_zero, one_mul] using h

/-- Actual Hecke ideal coefficients enter the rational Weil transformation
through the proved identity of the two convergent theta series. -/
theorem heckeTheta_adelic_transform
    (D : WeilData (Fin 2) MpR MpF MpA) (γ : SL(2, ℚ))
    (χ : OAI.SevenEighths.HeckeFamily.Character) (hχ : χ.residue ≠ 1) (τ : ℍ) :
    theta (D.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (OAI.SevenEighths.HeckeFamily.coefficients χ)))
        (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        (6 * heckeTheta χ τ) := by
  rw [eisensteinAdelicTheta_transform, theta_eisensteinFiniteTest_eq_six_heckeTheta χ hχ]

end ArtinMatthews
