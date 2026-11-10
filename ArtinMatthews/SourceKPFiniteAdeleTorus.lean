module

public import ArtinMatthews.SourceKPFiniteAdeleRationalSplit
public import ArtinMatthews.SourceKPCommRingDiagonal
public import ArtinMatthews.SourceFiniteKPRankOneTorus
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual adelic torus multiplier is the product of the local
squared cubic Hilbert symbols. All diagonal cochains are one. A cube
argument gives a genuinely split torus product, including at wild
places, and rational diagonal lifts have phase one. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPFinitePhase_diagonal (P : HeightOneSpectrum (𝓞 K)) (x : (P.adicCompletion K)ˣ) :
    sourceKPFinitePhase K hζ P (sourceGL2Diagonal x) = 1 :=
  sourceKPFinitePhase_zero_left K hζ P _ (by simp [sourceGL2Diagonal])

theorem sourceKPFiniteTwistedMultiplier_diagonal (P : HeightOneSpectrum (𝓞 K))
    (x y : (P.adicCompletion K)ˣ) :
    sourceKPFiniteTwistedMultiplier K hζ P (sourceGL2Diagonal x) (sourceGL2Diagonal y) =
      sourceFiniteKPHilbert K hζ P x y ^ 2 := by
  have hm : sourceGL2Diagonal x * sourceGL2Diagonal y = sourceGL2Diagonal (x * y) :=
    ((sourceGL2DiagonalHom (P.adicCompletion K)).map_mul x y).symm
  rw [sourceKPFiniteTwistedMultiplier, sourceKPCochainTwist,
    sourceKPFinitePhase_diagonal K hζ P x, sourceKPFinitePhase_diagonal K hζ P y, hm,
    sourceKPFinitePhase_diagonal, sourceFiniteKP2Multiplier_rankOne, one_mul, one_mul, div_one]

theorem sourceKPAdeleLocalMultiplier_diagonal (P : HeightOneSpectrum (𝓞 K)) (x y : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleLocalMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] x) (sourceKPDiagonalHom 𝔸ᶠ[K] y) P =
      (sourceKPRootsTransport K hζ P).symm
        (sourceFiniteKPHilbert K hζ P (Units.map (sourceKPAdeleEval K P).toMonoidHom x)
          (Units.map (sourceKPAdeleEval K P).toMonoidHom y) ^ 2) := by
  rw [sourceKPAdeleLocalMultiplier, sourceKPAdeleMatrixAt,
    sourceKPDiagonalHom_map, sourceKPDiagonalHom_map, sourceKPDiagonalHom_field, sourceKPDiagonalHom_field,
    sourceKPFiniteTwistedMultiplier_diagonal]

theorem sourceKPAdeleMultiplier_diagonal_cube_left (x y : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] (x ^ (3 : ℕ))) (sourceKPDiagonalHom 𝔸ᶠ[K] y) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier_diagonal, map_pow (Units.map (sourceKPAdeleEval K P).toMonoidHom),
    sourceFiniteKPHilbert_cube_left, one_pow, map_one]

theorem sourceKPAdeleMultiplier_diagonal_cube_right (x y : 𝔸ᶠ[K]ˣ) :
    sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] x) (sourceKPDiagonalHom 𝔸ᶠ[K] (y ^ (3 : ℕ))) = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [sourceKPAdeleLocalMultiplier_diagonal, map_pow (Units.map (sourceKPAdeleEval K P).toMonoidHom),
    sourceFiniteKPHilbert_cube_right, one_pow, map_one]

def sourceKPFiniteAdeleProjectiveDiagonalLift (x : 𝔸ᶠ[K]ˣ) : SourceKPFiniteAdeleProjective K hζ :=
  sourceKPFiniteAdeleProjectiveMk K hζ ⟨1, sourceKPDiagonalHom 𝔸ᶠ[K] x⟩

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_projection (x : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteAdeleProjectiveDiagonalLift K hζ x) =
      sourceKPProjectiveDiagonalHom 𝔸ᶠ[K] x := rfl

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_one :
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ 1 = 1 := by
  unfold sourceKPFiniteAdeleProjectiveDiagonalLift
  rw [map_one (sourceKPDiagonalHom 𝔸ᶠ[K])]
  exact (sourceKPFiniteAdeleProjectiveMk K hζ).map_one

private theorem sourceKPFiniteAdeleProjectiveDiagonalLift_mul_of_phase_one (x y : 𝔸ᶠ[K]ˣ)
    (h : sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] x) (sourceKPDiagonalHom 𝔸ᶠ[K] y) = 1) :
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ x * sourceKPFiniteAdeleProjectiveDiagonalLift K hζ y =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (x * y) := by
  unfold sourceKPFiniteAdeleProjectiveDiagonalLift
  rw [← map_mul]
  apply congrArg (sourceKPFiniteAdeleProjectiveMk K hζ)
  apply SourceKPFiniteAdeleCover.ext
  · change 1 * 1 * sourceKPAdeleMultiplier K hζ (sourceKPDiagonalHom 𝔸ᶠ[K] x)
      (sourceKPDiagonalHom 𝔸ᶠ[K] y) = 1
    rw [h, mul_one, mul_one]
  · exact ((sourceKPDiagonalHom 𝔸ᶠ[K]).map_mul x y).symm

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_cube_mul_left (x y : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (x ^ (3 : ℕ)) * sourceKPFiniteAdeleProjectiveDiagonalLift K hζ y =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (x ^ (3 : ℕ) * y) :=
  sourceKPFiniteAdeleProjectiveDiagonalLift_mul_of_phase_one K hζ _ _
    (sourceKPAdeleMultiplier_diagonal_cube_left K hζ x y)

theorem sourceKPFiniteAdeleProjectiveDiagonalLift_cube_mul_right (x y : 𝔸ᶠ[K]ˣ) :
    sourceKPFiniteAdeleProjectiveDiagonalLift K hζ x * sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (y ^ (3 : ℕ)) =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (x * y ^ (3 : ℕ)) :=
  sourceKPFiniteAdeleProjectiveDiagonalLift_mul_of_phase_one K hζ _ _
    (sourceKPAdeleMultiplier_diagonal_cube_right K hζ x y)

theorem sourceKPFiniteAdeleProjectiveRationalLift_diagonal (x : Kˣ) :
    sourceKPFiniteAdeleProjectiveRationalLift K hζ (sourceKPProjectiveDiagonalHom K x) =
      sourceKPFiniteAdeleProjectiveDiagonalLift K hζ (FiniteAdeleRing.unitEmbedding (𝓞 K) K x) := by
  change sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk (sourceKPDiagonalHom K x)) = _
  have hp : ∏ᶠ P, sourceKPRationalLocalPhase K hζ (sourceKPDiagonalHom K x) P = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro P
    rw [sourceKPRationalLocalPhase, sourceKPAdeleMatrixAt_rational, sourceKPDiagonalHom_map,
      sourceKPDiagonalHom_field, sourceKPFinitePhase_diagonal, map_one]
  have hb : sourceKPRationalDiagonal K (sourceKPDiagonalHom K x) =
      sourceKPDiagonalHom 𝔸ᶠ[K] (FiniteAdeleRing.unitEmbedding (𝓞 K) K x) :=
    sourceKPDiagonalHom_map (algebraMap K 𝔸ᶠ[K]) x
  rw [sourceKPFiniteAdeleProjectiveRationalLift_mk, hp, inv_one, hb]
  rfl

end
end ArtinMatthews
