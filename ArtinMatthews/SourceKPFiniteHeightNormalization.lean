module

public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceKPFiniteOrbit
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPIdeleNormFlow
public import ArtinMatthews.SourceKPAdelicBorelBand
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

/-! Height-one representatives for the actual finite-level fibers. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPFiniteMatrixHeightProduct_one :
    sourceKPFiniteMatrixHeightProduct K 1 = 1 := by
  apply finprod_eq_one_of_forall_eq_one
  intro P
  rw [map_one]
  exact sourceKPFiniteMatrixHeight_integral K P 1 (sourceKPIntegralMatrix_one _)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPArchMatrixHeight_one : sourceKPArchMatrixHeight K hζ 1 = 1 := by
  simp [sourceKPArchMatrixHeight, sourceArchHeight, sourceArchBottomNorm]

def sourceKPArchNormFlowMatrix (v₀ : InfinitePlace K) (t : ℝ) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  sourceKPDiagonalHom (InfiniteAdeleRing K)
    (sourceKPIdeleInfiniteUnit K (sourceKPIdeleNormFlow K hζ v₀ t))

theorem sourceKPArchNormFlowHeight (v₀ : InfinitePlace K) (t : ℝ) :
    sourceKPArchMatrixHeight K hζ (sourceKPArchNormFlowMatrix K hζ v₀ t) = Real.exp t := by
  let u := sourceKPIdeleNormFlow K hζ v₀ t
  have hp : sourceKPGL2ProductEquiv K (sourceKPDiagonalHom 𝔸[K] u) =
      (sourceKPArchNormFlowMatrix K hζ v₀ t, 1) := by
    rw [sourceKPGL2ProductEquiv_diagonal, sourceKPIdeleNormFlow_finite, map_one]
    rfl
  have hf := sourceKPAdelicHeight_pair K hζ (sourceKPArchNormFlowMatrix K hζ v₀ t) 1
  rw [← hp, MulEquiv.symm_apply_apply, sourceKPFiniteMatrixHeightProduct_one, mul_one] at hf
  have hu := sourceKPAdelicHeight_upper_diagonal K hζ 0 u
  rw [sourceKPUpperMatrix_zero, one_mul, sourceKPIdeleNormFlow_norm] at hu
  exact hf.symm.trans hu

theorem sourceKPAdelicCoverHeight_finite_normalize (v₀ : InfinitePlace K)
    (b : SourceKPFiniteAdeleProjective K hζ) :
    ∃ a : PGL(2, InfiniteAdeleRing K), sourceKPAdelicCoverHeight K hζ (a, b) = 1 := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ b)
  have hc : 0 < sourceKPFiniteMatrixHeightProduct K u := by
    have h := sourceKPAdelicCoverHeight_pos K hζ (ProjGenLinGroup.mk 1, b)
    rw [sourceKPAdelicCoverHeight_arch_matrix K hζ b u hu.symm 1,
      sourceKPArchMatrixHeight_one, one_mul] at h
    exact h
  refine ⟨ProjGenLinGroup.mk (sourceKPArchNormFlowMatrix K hζ v₀
    (-Real.log (sourceKPFiniteMatrixHeightProduct K u))), ?_⟩
  rw [sourceKPAdelicCoverHeight_arch_matrix K hζ b u hu.symm,
    sourceKPArchNormFlowHeight, Real.exp_neg, Real.exp_log hc, inv_mul_cancel₀ hc.ne']

theorem sourceKPFiniteLevelHeight_fiber_one (v₀ : InfinitePlace K)
    (b : SourceKPFiniteLevelFiber K hζ) :
    ∃ a : PGL(2, InfiniteAdeleRing K), sourceKPFiniteLevelHeight K hζ (a, b) = 1 := by
  induction b using Quotient.inductionOn with
  | _ b =>
    obtain ⟨a, ha⟩ := sourceKPAdelicCoverHeight_finite_normalize K hζ v₀ b
    exact ⟨a, ha⟩

theorem sourceKPFiniteOrbit_height_one_rep (v₀ : InfinitePlace K)
    (o : SourceKPFiniteOrbit K hζ) :
    ∃ q : SourceKPAdelicProjective K hζ, sourceKPAdelicCoverHeight K hζ q = 1 ∧
      sourceKPAutomorphicFiniteOrbit K hζ (sourceKPAutomorphicLevelMk K hζ q) = o := by
  induction o using Quotient.inductionOn with
  | _ b =>
    induction b using Quotient.inductionOn with
    | _ b =>
      obtain ⟨a, ha⟩ := sourceKPAdelicCoverHeight_finite_normalize K hζ v₀ b
      exact ⟨(a, b), ha, rfl⟩

end
end ArtinMatthews
