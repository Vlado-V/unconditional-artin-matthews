module

public import ArtinMatthews.SourceKPFiniteLevelTopology
public import ArtinMatthews.SourceArchSectionFactorization
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceArchSectionContinuity
public import ArtinMatthews.SourceEisensteinNonconstantInvariance
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

/-! The actual outgoing term descends continuously to the original finite level. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_continuous (s : ℂ) :
    Continuous (sourceArchSphericalProduct K hζ s) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin 2) (InfiniteAdeleRing K)))).continuous_iff.mpr
  exact sourceArchSphericalProduct_matrix_continuous K hζ s

theorem sourceKPAdelicTraceIntertwiner_arch_continuous {s : ℂ} (hs : 0 < s.re)
    (qf : SourceKPFiniteAdeleProjective K hζ) :
    Continuous (fun a : PGL(2, InfiniteAdeleRing K) => sourceKPAdelicTraceIntertwiner K hζ s (a,qf)) := by
  have hc : Continuous (fun a : PGL(2, InfiniteAdeleRing K) =>
      ((Real.pi : ℂ) / s) ^ Fintype.card (InfinitePlace K) *
        sourceArchSphericalProduct K hζ (-s) a * sourceKPFiniteIntertwiner K hζ s qf) :=
    (continuous_const.mul (sourceArchSphericalProduct_continuous K hζ (-s))).mul continuous_const
  exact hc.congr (fun a => (sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs (a,qf)).symm)

theorem sourceKPAdelicTraceIntertwiner_finite_right (s : ℂ)
    (g : SourceKPAdelicProjective K hζ) (k : sourceKPFiniteDeepMatrixGroup K) :
    sourceKPAdelicTraceIntertwiner K hζ s (g * sourceKPFiniteDeepCoverLift K hζ k) =
      sourceKPAdelicTraceIntertwiner K hζ s g :=
  sourceKPAdelicTraceIntertwiner_deepCompact_right K hζ s g
    ⟨sourceKPFiniteDeepCoverLift K hζ k, ⟨sourceKPFiniteDeepIntoAdelic K hζ k, rfl⟩⟩

def sourceKPFiniteLevelOutgoingEisenstein (s : ℂ) : SourceKPFiniteLevelSpace K hζ → ℂ :=
  sourceKPFiniteLevelDescend K hζ (sourceKPAdelicTraceIntertwiner K hζ s)
    (sourceKPAdelicTraceIntertwiner_finite_right K hζ s)

theorem sourceKPFiniteLevelOutgoingEisenstein_mk (s : ℂ) (g : SourceKPAdelicProjective K hζ) :
    sourceKPFiniteLevelOutgoingEisenstein K hζ s (sourceKPFiniteLevelMk K hζ g) =
      sourceKPAdelicTraceIntertwiner K hζ s g := rfl

theorem sourceKPFiniteLevelOutgoingEisenstein_continuous {s : ℂ} (hs : 0 < s.re) :
    Continuous (sourceKPFiniteLevelOutgoingEisenstein K hζ s) :=
  sourceKPFiniteLevelDescend_continuous K hζ _ _
    (sourceKPAdelicTraceIntertwiner_arch_continuous K hζ hs)

end
end ArtinMatthews
