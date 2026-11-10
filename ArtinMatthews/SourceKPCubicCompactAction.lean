module

public import ArtinMatthews.SourceKPAutomorphicL2
public import ArtinMatthews.SourceKPCubicCenterAction
public import ArtinMatthews.SourceKPAutomorphicCenterMeasure
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

/-! The cubic center action on the actual compact quotient and its measure. -/

namespace ArtinMatthews
open NumberField Matrix Topology MeasureTheory
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

instance sourceKPCubicCenter_finiteLevel_archRight_comm :
    SMulCommClass (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (rootsOfUnity 3 K)
      (SourceKPFiniteLevelSpace K hζ) where
  smul_comm h z x := by
    rcases x with ⟨a, b⟩
    simp only [sourceKPFiniteLevel_archRight_smul, sourceKPCubicCenter_finiteLevel_pair]

instance sourceKPCubicCenter_automorphic_archRight_comm :
    SMulCommClass (PGL(2, InfiniteAdeleRing K))ᵐᵒᵖ (rootsOfUnity 3 K)
      (SourceKPAutomorphicLevel K hζ) where
  smul_comm h z x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      change (Quotient.mk _ (h • (z • x)) : SourceKPAutomorphicLevel K hζ) =
        Quotient.mk _ (z • (h • x))
      exact congrArg (Quotient.mk _) (smul_comm h z x)

instance sourceKPCubicCenter_automorphic_compactRight_comm :
    SMulCommClass (SourceKPArchCompactRightGroup K hζ) (rootsOfUnity 3 K)
      (SourceKPAutomorphicLevel K hζ) where
  smul_comm k z x := smul_comm k.val z x

instance sourceKPCubicCenter_compactAction :
    MulAction (rootsOfUnity 3 K) (SourceKPAutomorphicCompactLevel K hζ) :=
  sourceCommutingOrbitAction (SourceKPArchCompactRightGroup K hζ) (rootsOfUnity 3 K)
    (SourceKPAutomorphicLevel K hζ)

theorem sourceKPCubicCenter_compact_mk (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicLevel K hζ) :
    z • sourceKPAutomorphicCompactMk K hζ x =
      sourceKPAutomorphicCompactMk K hζ (z • x) := rfl

instance sourceKPCubicCenter_compact_continuousSMul :
    ContinuousSMul (rootsOfUnity 3 K) (SourceKPAutomorphicCompactLevel K hζ) :=
  sourceCommutingOrbitAction_continuous (SourceKPArchCompactRightGroup K hζ)
    (rootsOfUnity 3 K) (SourceKPAutomorphicLevel K hζ)

theorem sourceKPCubicCenter_compact_continuous (z : rootsOfUnity 3 K) :
    Continuous (fun x : SourceKPAutomorphicCompactLevel K hζ => z • x) :=
  continuous_const_smul z

theorem sourceKPCubicCenter_compact_finiteOrbit (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPAutomorphicCompactFiniteOrbit K hζ (z • x) =
      z • sourceKPAutomorphicCompactFiniteOrbit K hζ x := by
  induction x using Quotient.inductionOn with
  | _ x => exact sourceKPCubicCenter_finiteOrbit_equivariant K hζ z x

theorem sourceKPCubicCenter_compact_map_preserving (z : rootsOfUnity 3 K)
    (ν : Measure (SourceKPAutomorphicLevel K hζ))
    (hν : MeasurePreserving (fun x : SourceKPAutomorphicLevel K hζ => z • x) ν ν) :
    MeasurePreserving (fun x : SourceKPAutomorphicCompactLevel K hζ => z • x)
      (Measure.map (sourceKPAutomorphicCompactMk K hζ) ν)
      (Measure.map (sourceKPAutomorphicCompactMk K hζ) ν) := by
  have hm := sourceKPAutomorphicCompactMk_measurable K hζ
  have hz := (sourceKPCubicCenter_compact_continuous K hζ z).measurable
  refine ⟨hz, ?_⟩
  rw [Measure.map_map hz hm]
  calc
    _ = Measure.map ((sourceKPAutomorphicCompactMk K hζ) ∘
        (fun x : SourceKPAutomorphicLevel K hζ => z • x)) ν := rfl
    _ = _ := by
      rw [← Measure.map_map hm hν.measurable, hν.map_eq]

theorem sourceKPAutomorphicCompactMeasure_center_preserving (z : rootsOfUnity 3 K)
    (μ : Measure (PGL(2, InfiniteAdeleRing K))) [μ.IsMulLeftInvariant] :
    MeasurePreserving (fun x : SourceKPAutomorphicCompactLevel K hζ => z • x)
      (sourceKPAutomorphicCompactMeasure K hζ μ) (sourceKPAutomorphicCompactMeasure K hζ μ) :=
  sourceKPCubicCenter_compact_map_preserving K hζ z _
    (sourceKPAutomorphicMeasure_center_preserving K hζ z μ)

end
end ArtinMatthews
