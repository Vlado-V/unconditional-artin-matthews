module

public import ArtinMatthews.SourceArchDiagonalLog
public import ArtinMatthews.SourceArchSingleRightAction
public import ArtinMatthews.SourceKPAdelicProjectiveHeight
public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceKPAdelicBaseCompactTopology
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

/-! Continuity of the actual cover height along the complex-place
right paths used by the Casimir. No topology on the finite cover is used. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Topology
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPCutoffArchMatrixSingle_continuous (v : InfinitePlace K) :
    Continuous (sourceArchMatrixSingle K hζ v) := by
  classical
  apply (sourceKPArchGLPiEquiv_symm_continuous K).comp
  apply continuous_pi
  intro w
  apply (sourceKPArchMatrixComplexEquiv_symm_continuous K hζ w).comp
  by_cases hw : w = v
  · subst w
    simp only [Pi.mulSingle_eq_same]
    exact continuous_id
  · simp only [Pi.mulSingle_eq_of_ne hw]
    exact continuous_const

theorem sourceKPAdelicCoverHeight_single_continuous
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    Continuous (fun a : GL (Fin 2) ℂ =>
      sourceKPAdelicCoverHeight K hζ (q*sourceArchGroupSingle K hζ v a)) := by
  obtain ⟨qArch,qf⟩ := q
  have hm : Continuous (fun a : GL (Fin 2) ℂ =>
      qArch*ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a)) :=
    continuous_const.mul (continuous_quot_mk.comp (sourceKPCutoffArchMatrixSingle_continuous K hζ v))
  change Continuous (fun a : GL (Fin 2) ℂ => sourceKPAdelicCoverHeight K hζ
    (qArch*ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),qf*1))
  simpa only [mul_one, Function.comp_def] using
    (sourceKPAdelicCoverHeight_arch_continuous K hζ qf).comp hm

theorem sourceKPCutoffUpperMatrix_continuous : Continuous (sourceKPUpperMatrix ℂ) := by
  have hc : Continuous (fun z : ℂ => (sourceKPUpperMatrix ℂ z : Matrix (Fin 2) (Fin 2) ℂ)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact continuous_const
    · exact continuous_id
    · exact continuous_const
    · exact continuous_const
  have hi (z : ℂ) : (sourceKPUpperMatrix ℂ z)⁻¹ = sourceKPUpperMatrix ℂ (-z) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← sourceKPUpperMatrix_add, add_neg_cancel, sourceKPUpperMatrix_zero]
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [hi, Function.comp_def] using hc.comp continuous_neg

theorem sourceKPCutoffPositiveDiagonal_continuous : Continuous sourceArchPositiveDiagonal := by
  have hc : Continuous (fun t : ℝ =>
      (sourceArchPositiveDiagonal t : Matrix (Fin 2) (Fin 2) ℂ)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact Complex.continuous_ofReal.comp Real.continuous_exp
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  have hi (t : ℝ) : (sourceArchPositiveDiagonal t)⁻¹ = sourceArchPositiveDiagonal (-t) := by
    apply inv_eq_of_mul_eq_one_right
    unfold sourceArchPositiveDiagonal
    rw [← map_mul]
    have he : Units.mk0 (Real.exp t : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)) *
        Units.mk0 (Real.exp (-t) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-t))) = 1 := by
      apply Units.ext
      change (Real.exp t : ℂ) * (Real.exp (-t) : ℂ) = 1
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    rw [he,map_one]
  apply Units.continuous_iff.mpr
  refine ⟨hc, ?_⟩
  simpa only [hi, Function.comp_def] using hc.comp continuous_neg

theorem sourceKPAdelicCoverHeight_upper_continuous
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) (z : ℂ) :
    Continuous (fun t : ℝ => sourceKPAdelicCoverHeight K hζ
      (q*sourceArchGroupSingle K hζ v (sourceKPUpperMatrix ℂ ((t : ℂ)*z)))) :=
  (sourceKPAdelicCoverHeight_single_continuous K hζ q v).comp
    (sourceKPCutoffUpperMatrix_continuous.comp (Complex.continuous_ofReal.mul_const z))

theorem sourceKPAdelicCoverHeight_diagonal_continuous
    (q : SourceKPAdelicProjective K hζ) (v : InfinitePlace K) :
    Continuous (fun t : ℝ => sourceKPAdelicCoverHeight K hζ
      (q*sourceArchGroupSingle K hζ v (sourceArchPositiveDiagonal t))) :=
  (sourceKPAdelicCoverHeight_single_continuous K hζ q v).comp
    sourceKPCutoffPositiveDiagonal_continuous

end
end ArtinMatthews
