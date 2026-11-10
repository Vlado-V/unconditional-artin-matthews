module

public import ArtinMatthews.SourceKPLocalBorelEmbedding
public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.SourceKPTameCentralAction
public import ArtinMatthews.SourceKPAdeleLocalEmbedding
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

/-! The genuine central and cube characters of the local normalized
Borel acting on the actual global induced torus carrier. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))

def sourceKPAdelicLocalTorusSection (y : (P.adicCompletion K)ˣ) : sourceKPAdelicCoveringTorus K hζ :=
  ⟨sourceKPAdelicProjectiveDiagonalLift K hζ (IdeleGroup.ofAdicCompletion (𝓞 K) K P y),
    sourceKPAdelicCoveringTorus_diagonal_mem K hζ _⟩

theorem sourceKPAdelicLocalBorel_diagonal (y : (P.adicCompletion K)ˣ) :
    sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelDiagonal K hζ P y) =
      sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicLocalTorusSection K hζ P y) := by
  apply Subtype.ext
  exact sourceKPAdelicLocalProjective_diagonal K hζ P y

theorem sourceKPAdelicLocalTorusSection_idele (y : (P.adicCompletion K)ˣ) :
    sourceKPAdelicTorusIdele K hζ (sourceKPAdelicLocalTorusSection K hζ P y) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K P y := by
  apply sourceKPProjectiveDiagonalHom_injective 𝔸[K]
  rw [← sourceKPAdelicTorusIdele_projection]
  exact sourceKPAdelicProjectiveDiagonalLift_projection K hζ _

theorem sourceKPAdelicLocalBorelRepresentation_diagonal (s : ℂ) (y : (P.adicCompletion K)ˣ)
    (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s (sourceFiniteKPProjectiveBorelDiagonal K hζ P y) v =
      (sourceKPIdeleComplexNorm K (1/2 : ℂ) (IdeleGroup.ofAdicCompletion (𝓞 K) K P y) : ℂ) •
        sourceKPAdelicTorusInducedRepresentation K hζ s (sourceKPAdelicLocalTorusSection K hζ P y) v := by
  change sourceKPAdelicNormalizedBorelRepresentation K hζ s
    (sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelDiagonal K hζ P y)) v = _
  rw [sourceKPAdelicLocalBorel_diagonal]
  change sourceKPAdelicBorelModularHalf K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicLocalTorusSection K hζ P y)) •
    sourceKPAdelicTorusInducedRepresentation K hζ s
      (sourceKPAdelicBorelTorusProjection K hζ
        (sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicLocalTorusSection K hζ P y))) v = _
  rw [sourceKPAdelicBorelTorusProjection_inclusion]
  congr 1
  change (sourceKPIdeleComplexNorm K (1/2 : ℂ)
    (sourceKPAdelicTorusIdele K hζ (sourceKPAdelicBorelTorusProjection K hζ
      (sourceKPAdelicBorelTorusInclusion K hζ (sourceKPAdelicLocalTorusSection K hζ P y)))) : ℂ) = _
  rw [sourceKPAdelicBorelTorusProjection_inclusion, sourceKPAdelicLocalTorusSection_idele]

theorem sourceKPAdelicLocalTorusSection_cube (y : (P.adicCompletion K)ˣ) :
    sourceKPAdelicLocalTorusSection K hζ P (y^3) =
      (sourceKPAdelicTorusInducingCube K hζ (sourceKPAdelicCubeTorusEquiv K hζ
        (1, sourceKPIdeleCube K (IdeleGroup.ofAdicCompletion (𝓞 K) K P y)))).val := by
  apply Subtype.ext
  rw [sourceKPAdelicTorusInducingCube_val, sourceKPAdelicCubeTorusEquiv_val]
  change sourceKPAdelicProjectiveDiagonalLift K hζ
      (IdeleGroup.ofAdicCompletion (𝓞 K) K P (y^3)) =
    sourceKPAdelicProjectiveCenter K hζ 1 * sourceKPAdelicProjectiveDiagonalLift K hζ
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K P y)^3)
  rw [map_one, one_mul, map_pow]

theorem sourceKPAdelicLocalBorelRepresentation_cube (s : ℂ) (y : (P.adicCompletion K)ˣ)
    (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y^3)) v =
      (sourceKPIdeleComplexNorm K (s+1/2) ((IdeleGroup.ofAdicCompletion (𝓞 K) K P y)^3) : ℂ) • v := by
  rw [sourceKPAdelicLocalBorelRepresentation_diagonal, sourceKPAdelicLocalTorusSection_cube,
    sourceKPAdelicTorusInducedRepresentation_cube, smul_smul,
    sourceKPAdelicParametricCharacter_equiv, map_one, one_mul, map_pow]
  change ((sourceKPIdeleComplexNorm K (1/2 : ℂ)
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K P y)^3) : ℂ) *
    (sourceKPIdeleComplexNorm K s
      ((IdeleGroup.ofAdicCompletion (𝓞 K) K P y)^3) : ℂ)) • v = _
  rw [mul_comm, ← Units.val_mul, ← sourceKPIdeleComplexNorm_add]

theorem sourceKPAdelicLocalBorel_center (z : rootsOfUnity 3 (P.adicCompletion K)) :
    sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelCenter K hζ P z) =
      sourceKPAdelicBorelCenter K hζ ((sourceKPRootsTransport K hζ P).symm z) := by
  apply Subtype.ext
  rw [sourceKPAdelicBorelCenter_val]
  exact sourceKPAdelicLocalProjective_center K hζ P z

theorem sourceKPAdelicLocalBorelRepresentation_center (s : ℂ)
    (z : rootsOfUnity 3 (P.adicCompletion K)) (v : SourceKPAdelicTorusInducedSpace K hζ s) :
    sourceKPAdelicLocalBorelRepresentation K hζ P s
      (sourceFiniteKPProjectiveBorelCenter K hζ P z) v = (sourceKPCentralComplex K hζ P z : ℂ) • v := by
  change sourceKPAdelicNormalizedBorelRepresentation K hζ s
    (sourceKPAdelicLocalBorel K hζ P (sourceFiniteKPProjectiveBorelCenter K hζ P z)) v = _
  rw [sourceKPAdelicLocalBorel_center, sourceKPAdelicNormalizedBorelRepresentation_center,
    ← sourceKPAdelicCentralComplex_transport K hζ P, MulEquiv.apply_symm_apply]

end
end ArtinMatthews
