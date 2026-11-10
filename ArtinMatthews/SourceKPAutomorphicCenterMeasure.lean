module

public import ArtinMatthews.SourceKPAutomorphicMeasureChoice
public import ArtinMatthews.SourceKPCubicCenterAction
public import ArtinMatthews.SourceKPCubicCenterComponents
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchComponentSubgroup_center_conjugacy (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    sourceKPArchComponentSubgroup K hζ (z • b) =
      sourceConjugateSubgroup (sourceKPArchComponentSubgroup K hζ b) 1 := by
  rw [sourceKPCubicCenter_archSubgroup]
  have he : (MulAut.conj (1 : PGL(2, InfiniteAdeleRing K))).toMonoidHom = MonoidHom.id _ := by
    ext g
    simp [MulAut.conj_apply]
  rw [sourceConjugateSubgroup,he,Subgroup.map_id]

theorem sourceKPArchComponentPushMeasure_center_map (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    Measure.map (fun x : SourceKPAutomorphicLevel K hζ => z • x)
      (sourceKPArchComponentPushMeasure K hζ b μ) =
      sourceKPArchComponentPushMeasure K hζ (z • b) μ := by
  have he := sourceKPArchComponentConjugacy_measurePreserving K hζ b (z • b) 1
    (sourceKPArchComponentSubgroup_center_conjugacy K hζ z b) μ
  have hz : Measurable (fun x : SourceKPAutomorphicLevel K hζ => z • x) :=
    (sourceKPCubicCenter_automorphic_continuous K hζ z).measurable
  unfold sourceKPArchComponentPushMeasure
  rw [Measure.map_map hz (sourceKPArchComponentEmbedding_measurable K hζ b),
    ← he.map_eq, Measure.map_map (sourceKPArchComponentEmbedding_measurable K hζ _) he.measurable]
  congr 1
  funext q
  induction q using Quotient.inductionOn with
  | _ a =>
    change z • sourceKPArchComponentPoint K hζ b a =
      sourceKPArchComponentEmbedding K hζ (z • b)
        (sourceKPArchComponentConjugacy K hζ b (z • b) 1
          (sourceKPArchComponentSubgroup_center_conjugacy K hζ z b)
          (sourceKPArchComponentQuotientMap K hζ b a))
    rw [sourceKPArchComponentConjugacy_mk]
    simpa only [one_mul,sourceKPArchComponentQuotientMap,sourceKPArchComponentEmbedding_mk]
      using sourceKPCubicCenter_component_point K hζ z b a

theorem sourceKPAutomorphicComponentMeasure_center_map (z : rootsOfUnity 3 K)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant]
    (i : SourceKPFiniteOrbit K hζ) :
    Measure.map (fun x : SourceKPAutomorphicLevel K hζ => z • x)
      (sourceKPAutomorphicComponentMeasure K hζ μ i) =
      sourceKPAutomorphicComponentMeasure K hζ μ (z • i) := by
  change Measure.map _ (sourceKPArchComponentPushMeasure K hζ
    (sourceKPFiniteOrbitRepresentative K hζ i) μ) = _
  rw [sourceKPArchComponentPushMeasure_center_map,sourceKPArchComponentPushMeasure_eq_component,
    ← sourceKPCubicCenter_finiteOrbit_mk,sourceKPFiniteOrbitRepresentative_spec]

theorem sourceKPAutomorphicMeasure_center_preserving (z : rootsOfUnity 3 K)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    MeasurePreserving (fun x : SourceKPAutomorphicLevel K hζ => z • x)
      (sourceKPAutomorphicMeasure K hζ μ) (sourceKPAutomorphicMeasure K hζ μ) := by
  have hz : Measurable (fun x : SourceKPAutomorphicLevel K hζ => z • x) :=
    (sourceKPCubicCenter_automorphic_continuous K hζ z).measurable
  refine ⟨hz,?_⟩
  ext U hU
  rw [Measure.map_apply hz hU,sourceKPAutomorphicMeasure,Measure.sum_apply _ (hU.preimage hz),
    Measure.sum_apply _ hU]
  calc
    ∑' i, sourceKPAutomorphicComponentMeasure K hζ μ i ((fun x => z • x) ⁻¹' U) =
        ∑' i, sourceKPAutomorphicComponentMeasure K hζ μ (z • i) U := by
      apply tsum_congr
      intro i
      rw [← Measure.map_apply hz hU,sourceKPAutomorphicComponentMeasure_center_map]
    _ = ∑' i, sourceKPAutomorphicComponentMeasure K hζ μ i U :=
      (sourceKPCubicCenterFiniteOrbitPerm K hζ z).tsum_eq
        (fun i : SourceKPFiniteOrbit K hζ => sourceKPAutomorphicComponentMeasure K hζ μ i U)

end
end ArtinMatthews
