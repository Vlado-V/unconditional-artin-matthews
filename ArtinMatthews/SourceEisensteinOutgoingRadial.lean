module

public import ArtinMatthews.SourceKPRadialHighFlow
public import ArtinMatthews.SourceKPAdelicTraceConstantTerm
public import ArtinMatthews.SourceEisensteinOutgoingHeight
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

/-! The genuine outgoing term has its exact norm scaling under the actual
balanced high-cusp radial flow. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicTraceIntertwiner_norm_radial {s : ℂ} (hs : 0 < s.re)
    (t : ℝ) (a : PGL(2, InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    ‖sourceKPAdelicTraceIntertwiner K hζ s (sourceKPArchRadialFlow K hζ t a,qf)‖ =
      sourceKPRadialHeightScale K t ^ (1 / 2 - s.re) *
        ‖sourceKPAdelicTraceIntertwiner K hζ s (a,qf)‖ := by
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective a
  rw [sourceKPArchRadialFlow_mk, sourceKPAdelicTraceIntertwiner_norm_height K hζ hs,
    sourceKPAdelicTraceIntertwiner_norm_height K hζ hs, sourceKPArchRadialFlowMatrix_height,
    Real.mul_rpow (Real.exp_pos _).le (by
      unfold sourceKPArchMatrixHeight
      exact Finset.prod_nonneg (fun _ _ => pow_nonneg (SourceArchJacquet.sourceArchHeight_pos _).le _))]
  change _ = Real.exp _ ^ (1 / 2 - s.re) * _
  ring

end
end ArtinMatthews
