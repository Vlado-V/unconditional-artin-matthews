module

public import ArtinMatthews.SourceAdelicHeightFibers
public import ArtinMatthews.SourceArchSingleRightAction
public import ArtinMatthews.SourceKPArchTranslatedProfile
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

/-! Smoothness of the literal adelic height in each complex-place
upper-half-space chart, with the other places retained in one explicit factor. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix OAI.CubicEisenstein Filter
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing ContDiff Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPAdelicOtherArchHeight (g : GL (Fin 2) (InfiniteAdeleRing K))
    (u : GL (Fin 2) 𝔸ᶠ[K]) (v : InfinitePlace K) : ℝ :=
  (∏ w ∈ Finset.univ.erase v, sourceArchHeight
    (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w)) ^ w.mult) *
      sourceKPFiniteMatrixHeightProduct K u

theorem sourceKPAdelicCoverHeight_single_factor
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u)
    (v : InfinitePlace K) (a : GL (Fin 2) ℂ) :
    sourceKPAdelicCoverHeight K hζ ((ProjGenLinGroup.mk g,qf)*sourceArchGroupSingle K hζ v a) =
      sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)*a)^v.mult *
        sourceKPAdelicOtherArchHeight K hζ g u v := by
  classical
  change sourceKPAdelicCoverHeight K hζ
    (ProjGenLinGroup.mk g*ProjGenLinGroup.mk (sourceArchMatrixSingle K hζ v a),qf*1) = _
  rw [mul_one,← map_mul,sourceKPAdelicCoverHeight_arch_matrix K hζ qf u hu]
  unfold sourceKPArchMatrixHeight
  simp only [map_mul,Pi.mul_apply,sourceArchMatrixSingle_at]
  have he : (∏ w : InfinitePlace K, sourceArchHeight
      (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w)*
        (Pi.mulSingle v a : InfinitePlace K → GL (Fin 2) ℂ) w)^w.mult) =
      sourceArchHeight (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)*a)^v.mult *
        ∏ w ∈ Finset.univ.erase v, sourceArchHeight
          (sourceKPArchMatrixComplexEquiv K hζ w (sourceArchGLPiEquiv K g w))^w.mult := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),Pi.mulSingle_eq_same]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    rw [Pi.mulSingle_eq_of_ne (Finset.mem_erase.mp hw).1,mul_one]
  rw [he,sourceKPAdelicOtherArchHeight,mul_assoc]

def sourceKPAdelicHeightUpperChart (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (p : EuclideanSpatial) : ℝ :=
  if hp : 0 < p 2 then sourceKPAdelicCoverHeight K hζ
    (q*sourceArchGroupSingle K hζ v
      (upperSection ((p 0 : ℂ)+(p 1 : ℂ)*Complex.I) (p 2) hp : GL (Fin 2) ℂ)) else 0

theorem sourceKPAdelicHeightUpperChart_factor
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (qf : SourceKPFiniteAdeleProjective K hζ)
    (u : GL (Fin 2) 𝔸ᶠ[K])
    (hu : sourceKPFiniteAdeleProjectiveProjection K hζ qf = ProjGenLinGroup.mk u)
    (v : InfinitePlace K) (p : EuclideanSpatial) (hp : 0 < p 2) :
    sourceKPAdelicHeightUpperChart K hζ (ProjGenLinGroup.mk g,qf) v p =
      (sourceArchTranslatedSectionChart 0
        (sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)) p).re ^ v.mult *
          sourceKPAdelicOtherArchHeight K hζ g u v := by
  rw [sourceKPAdelicHeightUpperChart,dite_eq_left hp,sourceKPAdelicCoverHeight_single_factor K hζ g qf u hu]
  congr 1
  congr 1
  simp only [sourceArchTranslatedSectionChart,dite_eq_left hp,sourceArchSphericalGL,
    mul_zero,zero_add,Complex.cpow_one,Complex.ofReal_re]

theorem sourceKPAdelicHeightUpperChart_contDiffAt (q : SourceKPAdelicProjective K hζ)
    (v : InfinitePlace K) (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt (ℝ) (∞ : ℕ∞ω) (sourceKPAdelicHeightUpperChart K hζ q v) p := by
  obtain ⟨qArch,qf⟩ := q
  obtain ⟨g,rfl⟩ := ProjGenLinGroup.mk_surjective qArch
  obtain ⟨u,hu⟩ := ProjGenLinGroup.mk_surjective (sourceKPFiniteAdeleProjectiveProjection K hζ qf)
  let a := sourceKPArchMatrixComplexEquiv K hζ v (sourceArchGLPiEquiv K g v)
  have hr : ContDiffAt (ℝ) (∞ : ℕ∞ω)
      (fun x => (sourceArchTranslatedSectionChart 0 a x).re) p :=
    Complex.reCLM.contDiff.contDiffAt.comp p (sourceArchTranslatedSectionChart_contDiffAt 0 a p hp)
  apply ((hr.pow v.mult).mul contDiffAt_const).congr_of_eventuallyEq
  have hpos : ∀ᶠ x : EuclideanSpatial in 𝓝 p, 0 < x 2 :=
    (show ContinuousAt (fun x : EuclideanSpatial => x 2) p by fun_prop).eventually_const_lt hp
  filter_upwards [hpos] with x hx
  exact sourceKPAdelicHeightUpperChart_factor K hζ g qf u hu.symm v x hx

end
end ArtinMatthews
