module

public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition
public import ArtinMatthews.SourcePrimeExponents
public import ArtinMatthews.SourceKPExteriorCofactor
public import ArtinMatthews.SourceKPIntegralGeneration
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! A principal diagonal times a retained vector has its literal rational
matrix at every exterior place. This chosen lift keeps the directed CRT
phase of the exterior diagonal. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup SourcePhysical
open scoped NumberField AdeleRing MatrixGroups Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "A" => GL (Fin 2) 𝔸ᶠ[K]
local notation "S" => sourceHilbertSet K S₀
local notation "F" => SourceKPFiniteAdeleCover K hζ
local notation "M" => sourceKPFiniteAdeleProjectiveMk K hζ
local notation "ev" => sourceKPAdeleMatrixAt K
local notation "tuple" => sourceKPAdelicRootSupportTuple K hζ

def sourceKPResidualPrincipalFiniteLift (m : Kˣ) (a : A) : F :=
  (⟨1,sourceKPRationalDiagonal K (sourceGL2Diagonal m)⟩ : F) *
    sourceKPAdelicRootSupportProduct K hζ a S

theorem sourceKPResidualPrincipalFiniteLift_mk (m : Kˣ) (a : A) :
    M (sourceKPResidualPrincipalFiniteLift K hζ S₀ m a) =
      (sourceKPAdelicProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m)).2 *
        (tuple 1 a S).2 := by
  rw [sourceKPResidualPrincipalFiniteLift,map_mul]
  have hD : sourceKPRationalDiagonal K (sourceGL2Diagonal m) =
      sourceKPDiagonalHom 𝔸ᶠ[K] (FiniteAdeleRing.unitEmbedding (𝓞 K) K m) := by
    rw [← sourceKPDiagonalHom_field]
    exact sourceKPDiagonalHom_map (algebraMap K 𝔸ᶠ[K]) m
  change M ⟨1,sourceKPRationalDiagonal K (sourceGL2Diagonal m)⟩ *
    M (sourceKPAdelicRootSupportProduct K hζ a S) =
      sourceKPFiniteAdeleProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K m) *
        M (sourceKPAdelicRootSupportProduct K hζ a S)
  rw [hD,sourceKPFiniteAdeleProjectiveRationalLift_diagonal]
  rfl

theorem sourceKPResidualPrincipalFiniteLift_exterior (m : Kˣ) (a : A)
    (P : SourceExteriorPrime K S₀) :
    ev P.val (sourceKPResidualPrincipalFiniteLift K hζ S₀ m a).base =
      sourceGL2Diagonal (Units.map (algebraMap K (P.val.adicCompletion K)).toMonoidHom m) := by
  let p := sourceKPFiniteAdeleProjection K hζ
  change ev P.val (p ((⟨1,sourceKPRationalDiagonal K (sourceGL2Diagonal m)⟩ : F) *
    sourceKPAdelicRootSupportProduct K hζ a S)) = _
  rw [map_mul p,map_mul (ev P.val),sourceKPAdelicRootSupportProduct_at_of_not_mem K hζ a S P.val P.property,
    mul_one]
  change ev P.val (sourceKPRationalDiagonal K (sourceGL2Diagonal m)) = _
  rw [sourceKPAdeleMatrixAt_rational,← sourceKPDiagonalHom_field,sourceKPDiagonalHom_map,
    sourceKPDiagonalHom_field]

theorem sourceKPResidualPrincipalFiniteLift_exterior_integral
    (a : A) (e : SourcePrimeExponents K S₀) (P : SourceExteriorPrime K S₀) (hP : e P = 0) :
    SourceKPIntegralMatrix (sourceKPFiniteVal K P.val)
      (ev P.val (sourceKPResidualPrincipalFiniteLift K hζ S₀ (sourcePrimeExponentUnit K hζ S₀ e) a).base) := by
  rw [sourceKPResidualPrincipalFiniteLift_exterior]
  apply sourceKPIntegralMatrix_diagonal
  change sourceKPFiniteVal K P.val (sourceKPCompletedExponentUnit K hζ S₀ P e : P.val.adicCompletion K) = 1
  rw [sourceKPCompletedExponentUnit_factor K hζ S₀ P e,hP,pow_zero,one_mul]
  exact sourceKPCompletedExponentUnit_erase_valuation K hζ S₀ P e

end
end ArtinMatthews
