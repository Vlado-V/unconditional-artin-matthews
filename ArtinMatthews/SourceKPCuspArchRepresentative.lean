module

public import ArtinMatthews.SourceKPCuspNativeUpperPoint
public import ArtinMatthews.SourceKPCompactEisensteinChart
public import ArtinMatthews.SourceKPCompactRationalTransport
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

/-! The literal representative-to-native chart projection and its upper
unipotent covariance, with the original archimedean Haar normalization. -/
namespace ArtinMatthews
open NumberField Matrix Module.Free MeasureTheory SourceHyperbolicGreen SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "G" => PGL(2, InfiniteAdeleRing K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V

local instance sourceNativeArchRepresentativeMeasurable :
    MeasurableSpace (SourceKPArchSymmetricSpace K hζ) := borel _
local instance sourceNativeArchRepresentativeBorel :
    BorelSpace (SourceKPArchSymmetricSpace K hζ) := ⟨rfl⟩

def sourceKPCuspArchRepresentativeCoordinates (g : G) : X :=
  sourceKPArchUpperEuclideanMap K
    (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk g))

theorem sourceKPCuspArchRepresentativeCoordinates_measurePreserving :
    MeasurePreserving (sourceKPCuspArchRepresentativeCoordinates K hζ)
      (sourceKPArchHaar K hζ) (productVolume V) :=
  (sourceKPArchUpperEuclideanMap_preserving K).comp
    ((sourceKPArchSymmetricHomeomorph_measurePreserving K hζ).comp
      (sourceKPArchHaar_projection K hζ))

theorem sourceKPCuspArchRepresentativeCoordinates_mul (a g : G) :
    sourceKPCuspArchRepresentativeCoordinates K hζ (a * g) =
      sourceKPArchEuclideanAction K hζ a (sourceKPCuspArchRepresentativeCoordinates K hζ g) := by
  unfold sourceKPCuspArchRepresentativeCoordinates sourceKPArchEuclideanAction
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  exact congrArg (sourceKPArchUpperEuclideanMap K)
    (sourceKPArchSymmetricHomeomorph_smul K hζ a (QuotientGroup.mk g))

theorem sourceKPCuspArchRepresentativeCoordinates_compact
    (qf : SourceKPFiniteAdeleProjective K hζ) (g : G) :
    sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
        (sourceKPCuspArchRepresentativeCoordinates K hζ g) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ (g,qf)) := by
  let b : SourceKPFiniteLevelFiber K hζ := QuotientGroup.mk qf
  change sourceKPUpperToCompact K hζ b (sourceKPArchEuclideanUpperMap K
    (sourceKPArchUpperEuclideanMap K
      (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk g)))) = _
  rw [sourceKPArchUpperEuclideanMap_left_inverse]
  exact sourceKPUpperToCompact_mk K hζ b g

theorem sourceKPCuspArchRepresentativeCoordinates_upper
    (qf : SourceKPFiniteAdeleProjective K hζ) (u : InfiniteAdeleRing K) (g : G) :
    sourceKPCompactCoordinateProjection K hζ (QuotientGroup.mk qf)
      (sourceKPArchEuclideanAction K hζ (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K])).1
        (sourceKPCuspArchRepresentativeCoordinates K hζ g)) =
      sourceKPAutomorphicCompactMk K hζ (sourceKPAutomorphicLevelMk K hζ
        (sourceKPAdelicUpperLift K hζ ((u,0) : 𝔸[K]) * (g,qf))) := by
  rw [← sourceKPCuspArchRepresentativeCoordinates_mul,
    sourceKPCuspArchRepresentativeCoordinates_compact]
  congr 2
  refine Prod.ext ?_ ?_
  · rfl
  · change qf = sourceKPFiniteAdeleUpperLift K hζ 0 * qf
    rw [sourceKPFiniteAdeleUpperLift_zero, one_mul]

theorem sourceKPCuspArchRepresentativeCoordinates_native
    (d : 𝓞 K) (hd : d ≠ 0) (x : ChooseBasisIndex ℤ (𝓞 K) → ℝ)
    (y : V → ℝ) (hy : ∀ v, 0 < y v) :
    sourceKPCuspArchRepresentativeCoordinates K hζ
        ((sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x)).1 *
          sourceKPCuspHeightSection K hζ y hy) =
      sourceKPCuspProductCoordinates K hζ d hd (x,y) := by
  let p := sourceKPCuspProductCoordinates K hζ d hd (x,y)
  have hp : ∀ v, 0 < p v 2 := fun v => by
    simpa only [p, sourceKPCuspProductCoordinates_height] using hy v
  let g := sourceArchUpperHalfspaceMatrix K hζ p hp
  have hg : ProjGenLinGroup.mk g =
      (sourceKPAdelicUpperLift K hζ (sourceKPCuspUnitCellAdelicPoint K d hd x)).1 *
        sourceKPCuspHeightSection K hζ y hy := by
    change ProjGenLinGroup.mk
      (sourceArchUpperHalfspaceMatrix K hζ (sourceKPCuspProductCoordinates K hζ d hd (x,y)) hp) = _
    rw [sourceKPCuspNativeUpperPoint_matrix K hζ d hd x y hy, map_mul]
    rfl
  rw [← hg]
  let a := sourceKPArchEuclideanUpperMap K p
  have ha : sourceKPArchUpperEuclideanMap K a = p :=
    sourceKPArchUpperEuclideanMap_right_inverse K p hp
  have hm : g = sourceKPArchUpperHalfSection K hζ a := by
    rw [← sourceKPArchUpperHalfspaceMatrix_euclidean K hζ a]
    unfold g
    congr 1
    exact ha.symm
  unfold sourceKPCuspArchRepresentativeCoordinates
  rw [hm]
  change sourceKPArchUpperEuclideanMap K
    (sourceKPArchSymmetricCoordinates K hζ (sourceKPArchSymmetricSection K hζ a)) = p
  rw [sourceKPArchSymmetricCoordinates_section, ha]

end
end ArtinMatthews
