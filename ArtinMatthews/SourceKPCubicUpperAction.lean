module

public import ArtinMatthews.SourceKPCubicCompactAction
public import ArtinMatthews.SourceKPCompactCoreCharts
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

/-! The actual cubic center permutes upper-half-space components with fixed coordinates. -/
namespace ArtinMatthews
open NumberField Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCubicCenter_upperToCompact (z : rootsOfUnity 3 K)
    (b : SourceKPFiniteLevelFiber K hζ) (p : SourceKPArchUpperHalfSpace K) :
    z • sourceKPUpperToCompact K hζ b p = sourceKPUpperToCompact K hζ (z • b) p := by
  obtain ⟨a, ha⟩ := Quotient.mk_surjective ((sourceKPArchSymmetricHomeomorph K hζ).symm p)
  have hp : sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a) = p :=
    (congrArg (sourceKPArchSymmetricHomeomorph K hζ) ha).trans
      ((sourceKPArchSymmetricHomeomorph K hζ).apply_symm_apply p)
  rw [← hp]
  change z • (sourceKPArithmeticUpperComponentHomeomorph K hζ b
      (Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a))) :
      SourceKPAutomorphicCompactLevel K hζ) =
    (sourceKPArithmeticUpperComponentHomeomorph K hζ (z • b)
      (Quotient.mk _ (sourceKPArchSymmetricHomeomorph K hζ (QuotientGroup.mk a))) :
      SourceKPAutomorphicCompactLevel K hζ)
  rw [sourceKPArithmeticUpperComponentHomeomorph_mk,
    sourceKPArithmeticUpperComponentHomeomorph_mk, sourceKPCubicCenter_compact_mk,
    sourceKPCubicCenter_component_point]

def sourceKPCubicCenterCompactHomeomorph (z : rootsOfUnity 3 K) :
    SourceKPAutomorphicCompactLevel K hζ ≃ₜ SourceKPAutomorphicCompactLevel K hζ :=
  Homeomorph.smul z

@[simp] theorem sourceKPCubicCenterCompactHomeomorph_apply (z : rootsOfUnity 3 K)
    (x : SourceKPAutomorphicCompactLevel K hζ) :
    sourceKPCubicCenterCompactHomeomorph K hζ z x = z • x := rfl

end
end ArtinMatthews
