module

public import ArtinMatthews.SourceKPFiniteAdeleProjective
public import ArtinMatthews.SourceKPRationalLiftPhase
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

/-! The actual rational splitting of the finite adelic cubic cover.
Its phase is the inverse cochain product, and the splitting descends
through the ordinary scalar quotient to the actual projective group. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section
variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPFiniteAdeleRationalLift : GL (Fin 2) K →* SourceKPFiniteAdeleCover K hζ where
  toFun g := ⟨sourceKPRationalLiftPhase K hζ g, sourceKPRationalDiagonal K g⟩
  map_one' := by
    apply SourceKPFiniteAdeleCover.ext
    · exact sourceKPRationalLiftPhase_one K hζ
    · exact map_one _
  map_mul' g h := by
    apply SourceKPFiniteAdeleCover.ext
    · exact sourceKPRationalLiftPhase_mul K hζ g h
    · exact map_mul _ _ _

theorem sourceKPFiniteAdeleRationalLift_phase (g : GL (Fin 2) K) :
    (sourceKPFiniteAdeleRationalLift K hζ g).central =
      (∏ᶠ P, sourceKPRationalLocalPhase K hζ g P)⁻¹ := rfl

theorem sourceKPFiniteAdeleRationalLift_projection (g : GL (Fin 2) K) :
    sourceKPFiniteAdeleProjection K hζ (sourceKPFiniteAdeleRationalLift K hζ g) =
      sourceKPRationalDiagonal K g := rfl

theorem sourceKPFiniteAdeleRationalLift_scalar (u : Kˣ) :
    sourceKPFiniteAdeleRationalLift K hζ (GeneralLinearGroup.scalar (Fin 2) u) =
      sourceKPFiniteAdeleScalar K hζ (FiniteAdeleRing.unitEmbedding (𝓞 K) K u) := by
  apply SourceKPFiniteAdeleCover.ext
  · exact sourceKPRationalLiftPhase_scalar K hζ u
  · exact GeneralLinearGroup.map_scalar (algebraMap K 𝔸ᶠ[K]) u

def sourceKPFiniteAdeleProjectiveRationalLift :
    PGL(2, K) →* SourceKPFiniteAdeleProjective K hζ :=
  QuotientGroup.lift _ ((sourceKPFiniteAdeleProjectiveMk K hζ).comp (sourceKPFiniteAdeleRationalLift K hζ)) (by
    intro g hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, rfl⟩ := hg
    change sourceKPFiniteAdeleProjectiveMk K hζ
      (sourceKPFiniteAdeleRationalLift K hζ (GeneralLinearGroup.scalar (Fin 2) u)) = 1
    rw [sourceKPFiniteAdeleRationalLift_scalar, sourceKPFiniteAdeleProjectiveMk_scalar])

theorem sourceKPFiniteAdeleProjectiveRationalLift_mk (g : GL (Fin 2) K) :
    sourceKPFiniteAdeleProjectiveRationalLift K hζ (ProjGenLinGroup.mk g) =
      sourceKPFiniteAdeleProjectiveMk K hζ
        ⟨(∏ᶠ P, sourceKPRationalLocalPhase K hζ g P)⁻¹, sourceKPRationalDiagonal K g⟩ := rfl

theorem sourceKPFiniteAdeleProjectiveRationalLift_projection (g : PGL(2, K)) :
    sourceKPFiniteAdeleProjectiveProjection K hζ (sourceKPFiniteAdeleProjectiveRationalLift K hζ g) =
      ProjGenLinGroup.map (algebraMap K 𝔸ᶠ[K]) g := by
  induction g using ProjGenLinGroup.induction_on with
  | mk g => rfl

end
end ArtinMatthews
