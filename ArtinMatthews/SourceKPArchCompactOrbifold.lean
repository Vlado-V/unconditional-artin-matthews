module

public import ArtinMatthews.SourceKPArchComponent
public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.CompactHomogeneousQuotient
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
public import ArtinMatthews.SourceKPArithmeticDiscreteness
public import ArtinMatthews.SourceKPArithmeticLocalQuotient
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
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The compact archimedean subgroup is the projection of the actual full
base compact subgroup. Its arithmetic homogeneous quotients retain finite
isotropy. -/
namespace ArtinMatthews
open NumberField Matrix Topology Filter
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPArchProjectiveMatrixMap : GL (Fin 2) 𝔸[K] →* PGL(2, InfiniteAdeleRing K) :=
  ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.fst _ _))

theorem sourceKPArchProjectiveMatrixMap_continuous :
    Continuous (sourceKPArchProjectiveMatrixMap K) :=
  continuous_quot_mk.comp continuous_fst.generalLinearGroup_map

def sourceKPArchBaseCompactSubgroup : Subgroup (PGL(2, InfiniteAdeleRing K)) :=
  (SourceKPAdelicBaseCompactMatrix K hζ).map (sourceKPArchProjectiveMatrixMap K)

theorem sourceKPArchBaseCompactSubgroup_isCompact :
    IsCompact (sourceKPArchBaseCompactSubgroup K hζ : Set (PGL(2, InfiniteAdeleRing K))) := by
  change IsCompact ((sourceKPArchProjectiveMatrixMap K) ''
    (SourceKPAdelicBaseCompactMatrix K hζ : Set (GL (Fin 2) 𝔸[K])))
  exact (SourceKPAdelicBaseCompactMatrix_isCompact K hζ).image
    (sourceKPArchProjectiveMatrixMap_continuous K)

abbrev SourceKPArchSymmetricSpace :=
  PGL(2, InfiniteAdeleRing K) ⧸ sourceKPArchBaseCompactSubgroup K hζ

instance sourceKPArchBaseCompactSubgroup_isClosed :
    IsClosed (sourceKPArchBaseCompactSubgroup K hζ : Set (PGL(2, InfiniteAdeleRing K))) :=
  (sourceKPArchBaseCompactSubgroup_isCompact K hζ).isClosed

instance sourceKPArchSymmetricSpace_t2 : T2Space (SourceKPArchSymmetricSpace K hζ) := by
  infer_instance

instance sourceKPArchSymmetricSpace_locallyCompact :
    LocallyCompactSpace (SourceKPArchSymmetricSpace K hζ) := by
  infer_instance

instance sourceKPArchSymmetricSpace_properlyDiscontinuous
    (b : SourceKPFiniteLevelFiber K hζ) :
    ProperlyDiscontinuousSMul (sourceKPArchComponentSubgroup K hζ b)
      (SourceKPArchSymmetricSpace K hζ) :=
  sourceCompactSubgroup_quotient_properlyDiscontinuous
    (sourceKPArchComponentSubgroup K hζ b) (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchBaseCompactSubgroup_isCompact K hζ)

theorem sourceKPArchSymmetricSpace_finite_stabilizer
    (b : SourceKPFiniteLevelFiber K hζ) (x : SourceKPArchSymmetricSpace K hζ) :
    (MulAction.stabilizer (sourceKPArchComponentSubgroup K hζ b) x :
      Set (sourceKPArchComponentSubgroup K hζ b)).Finite :=
  ProperlyDiscontinuousSMul.finite_stabilizer x

theorem sourceKPArchSymmetricSpace_disjoint_neighborhood
    (b : SourceKPFiniteLevelFiber K hζ) (x : SourceKPArchSymmetricSpace K hζ) :
    ∃ U ∈ 𝓝 x, ∀ γ : sourceKPArchComponentSubgroup K hζ b,
      γ • x ≠ x → Disjoint ((γ • ·) '' U) U :=
  sourceKPArchHomogeneous_disjoint_neighborhood K hζ b
    (sourceKPArchBaseCompactSubgroup K hζ)
    (sourceKPArchBaseCompactSubgroup_isCompact K hζ) x

end
end ArtinMatthews
