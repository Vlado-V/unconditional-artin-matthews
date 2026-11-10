module

public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceAdelicOrbitHeightTopology
public import ArtinMatthews.SourceEisensteinOutgoingFiniteLevel
public import ArtinMatthews.SourceKPArchComponent
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceEisensteinHighOutgoing
public import ArtinMatthews.SourceEisensteinOutgoingCoverHeight
public import ArtinMatthews.SourceKPFiniteHeightNormalization
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

/-! The actual outgoing term on one finite Borel orbit has the normalized
complex height power, with the original finite intertwiner as its coefficient. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceArchSphericalProduct_eq_height_cpow (s : ℂ)
    (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    sourceArchSphericalProduct K hζ s (ProjGenLinGroup.mk g) =
      (sourceKPArchMatrixHeight K hζ g : ℂ) ^ (s + 1 / 2) := by
  let := source_isTotallyComplex K hζ
  let height (v : InfinitePlace K) :=
    sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v))
  have hheight (v : InfinitePlace K) : 0 < height v := sourceArchHeight_pos _
  have hprod (V : Finset (InfinitePlace K)) :
      ((∏ v ∈ V, height v ^ v.mult : ℝ) : ℂ) ^ (s + 1 / 2) =
        ∏ v ∈ V, ((height v ^ v.mult : ℝ) : ℂ) ^ (s + 1 / 2) := by
    classical
    induction V using Finset.induction_on with
    | empty => simp
    | @insert v V hv ih =>
      rw [Finset.prod_insert hv, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (pow_nonneg (hheight v).le _)
          (Finset.prod_nonneg (fun w _ => pow_nonneg (hheight w).le _)),
        ih, Finset.prod_insert hv]
  rw [sourceArchSphericalProduct_mk, sourceKPArchMatrixHeight]
  rw [hprod Finset.univ]
  apply Finset.prod_congr rfl
  intro v _
  change (height v : ℂ) ^ (2 * s + 1) =
    ((height v ^ v.mult : ℝ) : ℂ) ^ (s + 1 / 2)
  rw [NumberField.IsTotallyComplex.mult_eq, ← Real.rpow_two,
    ← Complex.cpow_mul_ofReal_nonneg (hheight v).le]
  congr 1
  norm_num
  ring

theorem sourceKPAdelicTraceIntertwiner_eq_height_ratio {s : ℂ} (hs : 0 < s.re)
    (a : PGL(2, InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ) :
    sourceKPAdelicTraceIntertwiner K hζ s (a, qf) =
      sourceKPAdelicTraceIntertwiner K hζ s (1, qf) *
        ((sourceKPAdelicCoverHeight K hζ (a, qf) /
          sourceKPAdelicCoverHeight K hζ (1, qf) : ℝ) : ℂ) ^ (1 / 2 - s) := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective a
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  have hbase : sourceKPAdelicCoverHeight K hζ (1, qf) = sourceKPFiniteMatrixHeightProduct K u := by
    simpa only [map_one, sourceKPArchMatrixHeight_one, one_mul] using
      sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu.symm (1 : GL (Fin 2) (InfiniteAdeleRing K))
  have hratio : sourceKPAdelicCoverHeight K hζ (ProjGenLinGroup.mk g, qf) /
      sourceKPAdelicCoverHeight K hζ (1, qf) = sourceKPArchMatrixHeight K hζ g := by
    rw [sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu.symm, hbase]
    exact mul_div_cancel_right₀ _ (sourceKPFiniteMatrixHeightProduct_pos K hζ u).ne'
  rw [sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs (ProjGenLinGroup.mk g, qf),
    sourceKPAdelicTraceIntertwiner_at_finite K hζ hs, hratio,
    sourceArchSphericalProduct_eq_height_cpow]
  rw [show -s + 1 / 2 = 1 / 2 - s by ring]
  ring

theorem sourceKPFiniteLevelOutgoingEisenstein_eq_height_ratio {s : ℂ} (hs : 0 < s.re)
    (qf : SourceKPFiniteAdeleProjective K hζ) (x : SourceKPFiniteLevelSpace K hζ)
    (hOrbit : x.2 ∈ Set.range (fun γ : sourceKPRationalBorel K =>
      γ.val • (sourceKPFiniteLevelMk K hζ (1, qf)).2)) :
    sourceKPFiniteLevelOutgoingEisenstein K hζ s x =
      sourceKPAdelicTraceIntertwiner K hζ s (1, qf) *
        ((sourceKPFiniteLevelHeight K hζ x /
          sourceKPAdelicCoverHeight K hζ (1, qf) : ℝ) : ℂ) ^ (1 / 2 - s) := by
  obtain ⟨γ, hγ⟩ := hOrbit
  let y : SourceKPFiniteLevelSpace K hζ := γ.val⁻¹ • x
  have hy₂ : y.2 = (sourceKPFiniteLevelMk K hζ (1, qf)).2 := by
    change γ.val⁻¹ • x.2 = _
    rw [← hγ, inv_smul_smul]
  have hy : sourceKPFiniteLevelMk K hζ (y.1, qf) = y := Prod.ext rfl hy₂.symm
  have hm : sourceKPFiniteLevelOutgoingEisenstein K hζ s y =
      sourceKPFiniteLevelOutgoingEisenstein K hζ s x :=
    sourceKPFiniteLevelOutgoingEisenstein_rationalBorel K hζ s γ.val⁻¹ (inv_mem γ.property) x
  have hh : sourceKPFiniteLevelHeight K hζ y = sourceKPFiniteLevelHeight K hζ x :=
    sourceKPFiniteLevelHeight_rationalBorel K hζ γ.val⁻¹ (inv_mem γ.property) x
  rw [← hm, ← hh, ← hy, sourceKPFiniteLevelOutgoingEisenstein_mk, sourceKPFiniteLevelHeight_mk]
  exact sourceKPAdelicTraceIntertwiner_eq_height_ratio K hζ hs y.1 qf

end
end ArtinMatthews
