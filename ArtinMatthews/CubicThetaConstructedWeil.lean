module

public import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData
public import ArtinMatthews.CubicThetaAdelicIdentity
public import ArtinMatthews.CubicThetaWeilTransform
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


set_option backward.privateInPublic true
@[expose] public section

/-!
The actual constructed Weil representation for the two-dimensional Eisenstein
lattice. No existence of a representation, theta transformation, or CuspForm
is a hypothesis. Congruence eigenvalues of its finite operator remain separate.
-/
noncomputable section
namespace ArtinMatthews

open scoped MatrixGroups
open Complex UpperHalfPlane
open OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-- The existing explicit real/finite/adelic construction in dimension two. -/
def cubicThetaWeilData :=
  OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Constructed.WeilData.CM.weilData 2

/-- The actual Hecke ideal theta satisfies the constructed rational Weil
transformation with its finite operator left explicit. -/
theorem heckeTheta_constructed_transform (γ : SL(2, ℚ))
    (χ : OAI.SevenEighths.HeckeFamily.Character) (hχ : χ.residue ≠ 1) (τ : ℍ) :
    theta (cubicThetaWeilData.finiteAction (eisensteinSymplectic γ)
      (eisensteinFiniteTest (OAI.SevenEighths.HeckeFamily.coefficients χ)))
        (eisensteinSiegel (γ • τ)) 0 =
      halfDet (realBlocks (eisensteinSymplectic γ)) (eisensteinSiegel τ) *
        (6 * heckeTheta χ τ) :=
  heckeTheta_adelic_transform cubicThetaWeilData γ χ hχ τ

end ArtinMatthews
