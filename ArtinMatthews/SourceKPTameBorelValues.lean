module

public import ArtinMatthews.SourceKPIntegralResiduePhase
public import ArtinMatthews.SourceKPLocalUnitResidue
public import ArtinMatthews.SourceKPTameBorelRepresentation
public import ArtinMatthews.SourceKPExteriorTorusValues
public import ArtinMatthews.SourceKPTameOperatorBasis
public import ArtinMatthews.SourceKPTameTorusValues
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-! Exact upper-root and diagonal actions in the literal induced
realization. The modular half factor combines with the torus norm
factor to give the total exponent `-ord/3`. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups ValuativeRel
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceFiniteKPProjectiveBorelUpper (x : P.adicCompletion K) : SourceFiniteKPProjectiveBorel K hζ P :=
  sourceFiniteKPProjectiveBorelEquiv K hζ P
    (sourceFiniteKPNormalizedBorelLift K hζ P (sourceGL2Upper x)
      (sourceGL2NormalizedBorel_upper (P.adicCompletion K) x))

def sourceFiniteKPProjectiveBorelDiagonal (y : (P.adicCompletion K)ˣ) :
    SourceFiniteKPProjectiveBorel K hζ P :=
  sourceFiniteKPProjectiveBorelEquiv K hζ P
    (sourceFiniteKPNormalizedBorelLift K hζ P (sourceGL2Diagonal y)
      (sourceGL2NormalizedBorel_diagonal (P.adicCompletion K) y))

theorem sourceFiniteKPProjectiveBorelUpper_val (x : P.adicCompletion K) :
    (sourceFiniteKPProjectiveBorelUpper K hζ P x).val =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Upper x) := rfl

theorem sourceFiniteKPProjectiveBorelDiagonal_val (y : (P.adicCompletion K)ˣ) :
    (sourceFiniteKPProjectiveBorelDiagonal K hζ P y).val =
      sourceFiniteKP2ProjectiveLift K hζ P (sourceGL2Diagonal y) := rfl

variable (h6 : (6 : 𝓞 K) ∉ P.asIdeal) (π : (P.adicCompletion K)ˣ)
    (hπ : sourceKPFiniteVal K P (π : P.adicCompletion K) = WithZero.exp (-1 : ℤ))

theorem sourceKPTameBorelRepresentation_upper (x : P.adicCompletion K) (f : ZMod 3 → ℂ) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelUpper K hζ P x) f = f := by
  rw [sourceFiniteKPProjectiveBorelUpper, sourceKPTameBorelRepresentation_of_normalized]
  let b := sourceFiniteKPNormalizedBorelLift K hζ P (sourceGL2Upper x)
    (sourceGL2NormalizedBorel_upper (P.adicCompletion K) x)
  change sourceKPTameBorelHalf K hζ P b • (sourceKPTameTorusRepresentation K hζ P h6 π hπ
    (sourceFiniteKPNormalizedBorelToTorus K hζ P b) f) = _
  have hb : sourceKPFiniteVal K P (sourceFiniteKPNormalizedBorelBase K hζ P b : P.adicCompletion K) = 1 := by
    change sourceKPFiniteVal K P (GeneralLinearGroup.det (sourceGL2Upper x) : P.adicCompletion K) = 1
    rw [sourceGL2Upper_det, Units.val_one, map_one]
  have ht := sourceFiniteKPNormalizedBorelToTorus_lift K hζ P (sourceGL2Upper x)
    (sourceGL2NormalizedBorel_upper (P.adicCompletion K) x)
  change sourceFiniteKPNormalizedBorelToTorus K hζ P b = _ at ht
  have h1 : sourceFiniteKPRankOneLift K hζ P 1 = 1 := by
    apply Subtype.ext
    apply SourceFiniteKP2Cover.ext
    · rfl
    · exact (sourceGL2DiagonalHom (P.adicCompletion K)).map_one
  rw [sourceKPTameBorelHalf_of_unit K hζ P b hb, ht, sourceGL2Upper_det, h1, map_one, one_smul]
  rfl

theorem sourceKPTameBorelRepresentation_diagonal (y : (P.adicCompletion K)ˣ) (f : ZMod 3 → ℂ) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelDiagonal K hζ P y) f =
      sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ)
        (-(sourceKPValuationOrder (sourceKPFiniteVal K P) y : ℝ) / 2) •
      sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneLift K hζ P y) f := by
  rw [sourceFiniteKPProjectiveBorelDiagonal, sourceKPTameBorelRepresentation_of_normalized]
  let b := sourceFiniteKPNormalizedBorelLift K hζ P (sourceGL2Diagonal y)
    (sourceGL2NormalizedBorel_diagonal (P.adicCompletion K) y)
  change sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ)
    (-(sourceKPValuationOrder (sourceKPFiniteVal K P) (GeneralLinearGroup.det (sourceGL2Diagonal y)) : ℝ) / 2) •
    (sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPNormalizedBorelToTorus K hζ P b) f) = _
  have ht := sourceFiniteKPNormalizedBorelToTorus_lift K hζ P (sourceGL2Diagonal y)
    (sourceGL2NormalizedBorel_diagonal (P.adicCompletion K) y)
  change sourceFiniteKPNormalizedBorelToTorus K hζ P b = _ at ht
  rw [ht, sourceGL2Diagonal_det]

include hπ in
theorem sourceKPValuationOrder_uniformizer_unit (j : ℤ) (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPValuationOrder (sourceKPFiniteVal K P) (π ^ j * u) = j := by
  have ho := (sourceKPValuationOrder_eq (sourceKPFiniteVal K P) π 1).mpr hπ
  rw [sourceKPValuationOrder_mul, sourceKPValuationOrder_zpow, ho, mul_one,
    sourceKPValuationOrder_of_unit _ _ hu, add_zero]

theorem sourceKPTameTorusRepresentation_uniformizer_basis (j : ℤ) (i : ZMod 3) :
    sourceKPTameTorusRepresentation K hζ P h6 π hπ (sourceFiniteKPRankOneLift K hζ P (π ^ j))
        (sourceJacquetBasis i) =
      sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ) ((j : ℝ) / 6) •
        sourceJacquetBasis (i + (j : ZMod 3)) := by
  let ν := sourceKPFiniteVal K P
  let ι := sourceKPCentralComplex K hζ P
  let ρ := sourceKPTameUniformizerCharacter K hζ P π
  let b := sourceFiniteKPRankOneBase K hζ P (sourceFiniteKPRankOneLift K hζ P (π ^ j))
  change sourceKPTameOperator (Ideal.absNorm P.asIdeal : ℝ) (ι 1)
    (ρ (sourceKPUnitPart ν π b)) (sourceKPValuationOrder ν b) (sourceJacquetBasis i) = _
  have hb : b = π ^ j := sourceFiniteKPRankOneLift_base K hζ P _
  have ho := (sourceKPValuationOrder_eq ν π 1).mpr hπ
  rw [hb, sourceKPValuationOrder_zpow, ho, mul_one, sourceKPUnitPart_of_uniformizer_zpow ν π hπ,
    map_one ρ, map_one ι, sourceKPTameOperator_basis, sourceKPCubicPower_one]
  simp only [Units.val_one, one_mul, mul_one]

theorem sourceKPTameBorelRepresentation_uniformizer_basis (j : ℤ) (i : ZMod 3) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (π ^ j))
        (sourceJacquetBasis i) =
      sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ) (-(j : ℝ) / 3) •
        sourceJacquetBasis (i + (j : ZMod 3)) := by
  have hQ : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))
  have ho := (sourceKPValuationOrder_eq (sourceKPFiniteVal K P) π 1).mpr hπ
  rw [sourceKPTameBorelRepresentation_diagonal, sourceKPTameTorusRepresentation_uniformizer_basis,
    sourceKPValuationOrder_zpow, ho, mul_one, smul_smul, ← sourceJacquetScale_add hQ]
  rw [show (-(j : ℝ) / 2 + (j : ℝ) / 6) = -(j : ℝ) / 3 by ring]

theorem sourceKPTameBorelRepresentation_uniformizer_unit_basis_zero (j : ℤ) (u : (P.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K P (u : P.adicCompletion K) = 1) :
    sourceKPTameBorelRepresentation K hζ P h6 π hπ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (π ^ j * u))
        (sourceJacquetBasis 0) =
      (sourceJacquetScale (Ideal.absNorm P.asIdeal : ℝ) (-(j : ℝ) / 3) *
        ((sourceKPTameUniformizerCharacter K hζ P π u ^ (-j) : ℂˣ) : ℂ)) •
        sourceJacquetBasis (j : ZMod 3) := by
  have hQ : 0 < (Ideal.absNorm P.asIdeal : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot))
  rw [sourceKPTameBorelRepresentation_diagonal,
    sourceKPTameTorusRepresentation_uniformizer_unit K hζ P h6 π hπ j u hu,
    sourceKPValuationOrder_uniformizer_unit K P π hπ j u hu, smul_smul,
    ← mul_assoc, ← sourceJacquetScale_add hQ]
  rw [show (-(j : ℝ) / 2 + (j : ℝ) / 6) = -(j : ℝ) / 3 by ring]

open AllowedGenerators VaryingKummerAnalytic

variable (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (p : SourceExteriorPrime K S₀)

theorem sourceKPTameExteriorBorel_diagonal_basis_zero (j : ℤ) (u : (p.val.adicCompletion K)ˣ)
    (hu : sourceKPFiniteVal K p.val (u : p.val.adicCompletion K) = 1) :
    sourceKPTameBorelRepresentation K hζ p.val (source_exterior_six_not_mem K S₀ p.val p.property)
      (sourceKPTameExteriorUniformizer K hζ S₀ p) (sourceKPTameExteriorUniformizer_valuation K hζ S₀ p)
      (sourceFiniteKPProjectiveBorelDiagonal K hζ p.val ((sourceKPTameExteriorUniformizer K hζ S₀ p) ^ j * u))
      (sourceJacquetBasis 0) =
      (sourceJacquetScale (Ideal.absNorm p.val.asIdeal : ℝ) (-(j : ℝ) / 3) *
        reflectionPrimeCharacters K hζ S₀ p (sourceKPLocalUnitResidue K p.val u hu) ^ (2 * j)) •
        sourceJacquetBasis (j : ZMod 3) := by
  rw [sourceKPTameBorelRepresentation_uniformizer_unit_basis_zero _ _ _ _ _ _ j u hu,
    Units.val_zpow_eq_zpow_val, sourceKPTameExteriorCharacter_residue K hζ S₀ p u hu, ← _root_.zpow_mul]
  rw [show (-2 : ℤ) * (-j) = 2 * j by ring]

end
end ArtinMatthews
